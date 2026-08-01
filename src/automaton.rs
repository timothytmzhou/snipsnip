use std::collections::{HashMap, HashSet, VecDeque};

use egglog::{EGraph, SerializeConfig};
use thiserror::Error;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StateId(pub(crate) u32);

impl StateId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TreeTransition {
    pub constructor: String,
    pub children: Vec<StateId>,
    pub output: StateId,
}

#[derive(Clone, Debug, Default)]
pub struct RegularTreeGrammar {
    state_names: Vec<String>,
    transitions: Vec<TreeTransition>,
}

#[derive(Debug, Error)]
pub enum AutomatonError {
    #[error("egglog program failed: {0}")]
    Egglog(String),
    #[error("invalid distinguished binding `{binding}`: {reason}")]
    InvalidBinding { binding: String, reason: String },
    #[error("the distinguished value has non-equality sort `{0}`")]
    NonEqualitySort(String),
    #[error("egglog 2.0 serialization does not support sort names containing `-`: `{0}`")]
    UnsupportedSortName(String),
    #[error("egglog serialization was incomplete: {0}")]
    IncompleteSerialization(String),
    #[error("the distinguished e-class was absent from the serialized e-graph")]
    MissingRootClass,
}

impl RegularTreeGrammar {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_state(&mut self, name: impl Into<String>) -> StateId {
        let id = StateId(
            u32::try_from(self.state_names.len()).expect("more than u32::MAX automaton states"),
        );
        self.state_names.push(name.into());
        id
    }

    pub fn add_transition(
        &mut self,
        constructor: impl Into<String>,
        children: impl Into<Vec<StateId>>,
        output: StateId,
    ) {
        let children = children.into();
        assert!(output.index() < self.state_names.len());
        assert!(
            children
                .iter()
                .all(|state| state.index() < self.state_names.len())
        );
        self.transitions.push(TreeTransition {
            constructor: constructor.into(),
            children,
            output,
        });
    }

    pub fn state_name(&self, state: StateId) -> &str {
        &self.state_names[state.index()]
    }

    pub fn state_count(&self) -> usize {
        self.state_names.len()
    }

    pub fn transitions(&self) -> &[TreeTransition] {
        &self.transitions
    }

    /// Loads and freezes an egglog program, then extracts the regular tree grammar
    /// rooted at an existing global binding.
    ///
    /// `binding` must name a value created by the program (for example `$root`);
    /// constructor expressions are rejected so that a fresh, unsaturated term cannot
    /// accidentally be inserted after the user's final `(run ...)`.
    pub fn from_egglog(program: &str, binding: &str) -> Result<(Self, StateId), AutomatonError> {
        if binding.trim().is_empty() {
            return Err(AutomatonError::InvalidBinding {
                binding: binding.to_owned(),
                reason: "expected a nonempty global name".to_owned(),
            });
        }

        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, program)
            .map_err(|error| AutomatonError::Egglog(error.to_string()))?;
        let binding_source = if binding.starts_with('$') {
            binding.to_owned()
        } else {
            format!("${binding}")
        };
        let expression = egraph
            .parser
            .get_expr_from_string(None, &binding_source)
            .map_err(|error| AutomatonError::InvalidBinding {
                binding: binding.to_owned(),
                reason: error.to_string(),
            })?;
        if !matches!(expression, egglog::ast::Expr::Var(_, _)) {
            return Err(AutomatonError::InvalidBinding {
                binding: binding.to_owned(),
                reason: "expected one global name, not a constructor expression".to_owned(),
            });
        }
        let (sort, value) =
            egraph
                .eval_expr(&expression)
                .map_err(|error| AutomatonError::InvalidBinding {
                    binding: binding.to_owned(),
                    reason: error.to_string(),
                })?;
        if !sort.is_eq_sort() {
            return Err(AutomatonError::NonEqualitySort(sort.name().to_string()));
        }
        let mut unsupported_sorts = egraph
            .get_arcsorts_by(|candidate| candidate.name().contains('-'))
            .into_iter()
            .map(|candidate| candidate.name().to_owned())
            .collect::<Vec<_>>();
        unsupported_sorts.sort_unstable();
        if let Some(name) = unsupported_sorts.into_iter().next() {
            // egglog 2.0's serializer asserts on such a tag, including for an
            // otherwise irrelevant class. Convert that dependency limitation to
            // a normal library error before calling it.
            return Err(AutomatonError::UnsupportedSortName(name));
        }
        let value = egraph.get_canonical_value(value, &sort);
        let serialized = egraph.serialize(SerializeConfig {
            root_eclasses: vec![(sort, value)],
            ..SerializeConfig::default()
        });
        if !serialized.is_complete() {
            return Err(AutomatonError::IncompleteSerialization(
                serialized.omitted_description(),
            ));
        }
        let graph = serialized.egraph;
        let root_class = graph
            .root_eclasses
            .first()
            .ok_or(AutomatonError::MissingRootClass)?
            .to_string();

        let mut nodes_by_class: HashMap<String, Vec<_>> = HashMap::new();
        for node in graph.nodes.values() {
            nodes_by_class
                .entry(node.eclass.to_string())
                .or_default()
                .push(node);
        }

        let mut result = Self::new();
        let mut state_by_class = HashMap::<String, StateId>::new();
        let root = intern_state(&mut result, &mut state_by_class, &root_class);
        let mut queue = VecDeque::from([root_class.clone()]);
        let mut visited = HashSet::new();
        let mut transitions = HashSet::new();

        while let Some(class) = queue.pop_front() {
            if !visited.insert(class.clone()) {
                continue;
            }
            let output = intern_state(&mut result, &mut state_by_class, &class);
            let Some(nodes) = nodes_by_class.get(&class) else {
                continue;
            };
            for node in nodes {
                if node.op == "[...]" {
                    continue;
                }
                let mut children = Vec::with_capacity(node.children.len());
                let mut complete = true;
                for child_node in &node.children {
                    let Some(child) = graph.nodes.get(child_node) else {
                        complete = false;
                        break;
                    };
                    let child_class = child.eclass.to_string();
                    children.push(intern_state(&mut result, &mut state_by_class, &child_class));
                    queue.push_back(child_class);
                }
                if !complete {
                    continue;
                }
                transitions.insert(TreeTransition {
                    constructor: node.op.clone(),
                    children,
                    output,
                });
            }
        }

        result.transitions = transitions.into_iter().collect();
        result.transitions.sort_by(|left, right| {
            (&left.constructor, &left.children, left.output).cmp(&(
                &right.constructor,
                &right.children,
                right.output,
            ))
        });
        Ok((result, root))
    }
}

fn intern_state(
    grammar: &mut RegularTreeGrammar,
    states: &mut HashMap<String, StateId>,
    class: &str,
) -> StateId {
    if let Some(state) = states.get(class) {
        *state
    } else {
        let state = grammar.add_state(class);
        states.insert(class.to_owned(), state);
        state
    }
}
