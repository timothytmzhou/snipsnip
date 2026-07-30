use crate::ast::Ast;
use crate::egraph::{ChildValue, ClassId, EGraph, ENode, InsertRef};
use crate::grammar::{Grammar, GrammarSymbol, LexemeValue, ProductionId};
use crate::parser::{HoleId, PatternStep};
use std::collections::{HashMap, HashSet};

/// One constructor application that became fully concrete, named by the hole
/// it replaced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletedNode {
    pub hole: HoleId,
    pub constructor: String,
    pub children: Vec<InsertRef>,
}

/// Decides, incrementally, whether the prefix pattern has a completion
/// equal to the root tree; holes are constrained by their grammar sorts.
pub struct Matcher {
    root: Ast,
    steps: Vec<PatternStep>,
    state: State,
}

/// Everything derived from the current e-graph; rebuilt by `refresh`.
struct State {
    root_class: Option<ClassId>,
    derives: HashSet<(String, ClassId)>,
    holes: HashMap<HoleId, Hole>,
    nodes: HashMap<HoleId, PatternNode>,
    realizable: bool,
}

/// Where a hole or node hangs: under which node, at which child index.
type Parent = Option<(HoleId, usize)>;

/// An open hole and the e-classes its subtree may land in.
struct Hole {
    candidate_classes: HashSet<ClassId>,
    parent: Parent,
}

/// A predicted constructor with children still being filled, keyed by the
/// hole it replaced; `candidate_nodes` are the e-nodes still compatible.
struct PatternNode {
    constructor: String,
    children: Vec<Child>,
    parent: Parent,
    candidate_nodes: Vec<ENode>,
}

enum Child {
    Hole(HoleId),
    Filled(InsertRef),
}

impl Matcher {
    /// A matcher for the query (start hole 0, root tree).
    pub fn new(root: Ast, egraph: &EGraph, grammar: &Grammar) -> Matcher {
        let mut matcher = Matcher {
            root,
            steps: Vec::new(),
            state: State::empty(),
        };
        matcher.refresh(egraph, grammar);
        matcher
    }

    /// Applies the steps of one lexeme; returns the completions they caused.
    pub fn advance(
        &mut self,
        egraph: &EGraph,
        grammar: &Grammar,
        steps: &[PatternStep],
    ) -> Vec<CompletedNode> {
        let mut completed = Vec::new();
        for step in steps {
            self.steps.push(step.clone());
            self.state.apply(egraph, grammar, step, &mut completed);
        }
        completed
    }

    /// Recomputes everything against the current e-graph by replaying steps.
    pub fn refresh(&mut self, egraph: &EGraph, grammar: &Grammar) {
        let mut state = State::empty();
        state.begin(egraph, grammar, &self.root);
        let mut already_inserted = Vec::new();
        for step in &self.steps {
            state.apply(egraph, grammar, step, &mut already_inserted);
        }
        self.state = state;
    }

    /// Is some completion of the pattern equal to the root tree?
    pub fn realizable(&self) -> bool {
        self.state.realizable
    }
}

impl State {
    fn empty() -> State {
        State {
            root_class: None,
            derives: HashSet::new(),
            holes: HashMap::new(),
            nodes: HashMap::new(),
            realizable: false,
        }
    }

    /// Sets up the start hole against the current e-graph.
    fn begin(&mut self, egraph: &EGraph, grammar: &Grammar, root: &Ast) {
        self.root_class = egraph.class_of(root);
        self.derives = derives_relation(egraph, grammar);
        let mut candidates = HashSet::new();
        if let Some(class) = &self.root_class {
            let start = grammar.start().to_string();
            if self.derives.contains(&(start, class.clone())) {
                candidates.insert(class.clone());
            }
        }
        self.realizable = !candidates.is_empty();
        self.holes.insert(
            0,
            Hole {
                candidate_classes: candidates,
                parent: None,
            },
        );
    }

    /// Applies one step, maintaining holes, nodes, and realizability.
    fn apply(
        &mut self,
        egraph: &EGraph,
        grammar: &Grammar,
        step: &PatternStep,
        completed: &mut Vec<CompletedNode>,
    ) {
        match step {
            PatternStep::Predict {
                hole,
                production,
                child_holes,
            } => self.predict(egraph, grammar, *hole, *production, child_holes, completed),
            PatternStep::Read { hole, lexeme } => {
                let (reference, value) = match &lexeme.value {
                    LexemeValue::Number(n) => (InsertRef::Number(*n), ChildValue::Number(*n)),
                    LexemeValue::Text(s) => {
                        (InsertRef::Text(s.clone()), ChildValue::Text(s.clone()))
                    }
                };
                let parent = self.holes.remove(hole).and_then(|hole| hole.parent);
                self.fill(parent, reference, Some(value), completed);
            }
        }
    }

    /// Replaces a hole by a production's constructor with fresh child holes.
    fn predict(
        &mut self,
        egraph: &EGraph,
        grammar: &Grammar,
        hole: HoleId,
        production: ProductionId,
        child_holes: &[HoleId],
        completed: &mut Vec<CompletedNode>,
    ) {
        let Some(replaced) = self.holes.remove(&hole) else {
            self.realizable = false;
            return;
        };
        let selected = selected_symbols(grammar, production);
        let constructor = grammar.production(production).constructor.clone();
        let candidate_nodes: Vec<ENode> = replaced
            .candidate_classes
            .iter()
            .flat_map(|class| egraph.nodes_in_class(&constructor, class))
            .filter(|node| self.compatible(node, &selected))
            .collect();
        if candidate_nodes.is_empty() {
            self.realizable = false;
        }
        for (index, child_hole) in child_holes.iter().enumerate() {
            self.holes.insert(
                *child_hole,
                Hole {
                    candidate_classes: project_classes(&candidate_nodes, index),
                    parent: Some((hole, index)),
                },
            );
        }
        self.nodes.insert(
            hole,
            PatternNode {
                constructor,
                children: child_holes.iter().map(|id| Child::Hole(*id)).collect(),
                parent: replaced.parent,
                candidate_nodes,
            },
        );
        if child_holes.is_empty() {
            self.complete(hole, completed);
        }
    }

    /// Every selected child of the e-node must be reachable by its grammar sort.
    fn compatible(&self, node: &ENode, selected: &[GrammarSymbol]) -> bool {
        node.children.len() == selected.len()
            && selected
                .iter()
                .enumerate()
                .all(|(index, symbol)| match (symbol, &node.children[index]) {
                    (GrammarSymbol::Nonterminal(name), ChildValue::Class(class)) => {
                        self.derives.contains(&(name.clone(), class.clone()))
                    }
                    (GrammarSymbol::LexemeKind(_), ChildValue::Class(_)) => false,
                    (GrammarSymbol::LexemeKind(_), _) => true,
                    (GrammarSymbol::Nonterminal(_), _) => false,
                })
    }

    /// Records a concrete child, re-narrows the open siblings, and cascades.
    fn fill(
        &mut self,
        parent: Parent,
        reference: InsertRef,
        value: Option<ChildValue>,
        completed: &mut Vec<CompletedNode>,
    ) {
        let Some((owner, index)) = parent else {
            self.realizable = match (&value, &self.root_class) {
                (Some(ChildValue::Class(class)), Some(root)) => class == root,
                _ => false,
            };
            return;
        };
        let node = self.nodes.get_mut(&owner).expect("parent node exists");
        node.children[index] = Child::Filled(reference);
        node.candidate_nodes
            .retain(|candidate| Some(&candidate.children[index]) == value.as_ref());
        if node.candidate_nodes.is_empty() {
            self.realizable = false;
        }
        let open_siblings: Vec<(usize, HoleId)> = node
            .children
            .iter()
            .enumerate()
            .filter_map(|(i, child)| match child {
                Child::Hole(id) => Some((i, *id)),
                Child::Filled(_) => None,
            })
            .collect();
        if open_siblings.is_empty() {
            self.complete(owner, completed);
            return;
        }
        for (i, id) in open_siblings {
            let classes = project_classes(&self.nodes[&owner].candidate_nodes, i);
            if let Some(hole) = self.holes.get_mut(&id) {
                hole.candidate_classes = classes;
            }
        }
    }

    /// All children are concrete: report the completion and fill the parent.
    fn complete(&mut self, owner: HoleId, completed: &mut Vec<CompletedNode>) {
        let node = self.nodes.remove(&owner).expect("node exists");
        let children = node
            .children
            .into_iter()
            .map(|child| match child {
                Child::Filled(reference) => reference,
                Child::Hole(_) => unreachable!(),
            })
            .collect();
        completed.push(CompletedNode {
            hole: owner,
            constructor: node.constructor,
            children,
        });
        let value = node
            .candidate_nodes
            .first()
            .map(|candidate| ChildValue::Class(candidate.class.clone()));
        self.fill(node.parent, InsertRef::Node(owner), value, completed);
    }
}

/// The classes offered at one child position across the candidate e-nodes.
fn project_classes(candidates: &[ENode], index: usize) -> HashSet<ClassId> {
    candidates
        .iter()
        .filter_map(|node| match &node.children[index] {
            ChildValue::Class(class) => Some(class.clone()),
            _ => None,
        })
        .collect()
}

/// The symbols at a production's selected positions.
fn selected_symbols(grammar: &Grammar, production: ProductionId) -> Vec<GrammarSymbol> {
    let spec = grammar.production(production);
    spec.selected_positions
        .iter()
        .map(|position| spec.symbols[position - 1].clone())
        .collect()
}

/// All pairs (nonterminal, class) whose tree language reaches the class.
fn derives_relation(egraph: &EGraph, grammar: &Grammar) -> HashSet<(String, ClassId)> {
    let mut derives: HashSet<(String, ClassId)> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for nonterminal in grammar.nonterminals() {
            for production in grammar.productions_of(&nonterminal) {
                let selected = selected_symbols(grammar, production);
                let constructor = &grammar.production(production).constructor;
                for node in egraph.nodes_of_constructor(constructor) {
                    if node.children.len() != selected.len() {
                        continue;
                    }
                    let reachable = selected.iter().enumerate().all(|(index, symbol)| {
                        match (symbol, &node.children[index]) {
                            (GrammarSymbol::Nonterminal(name), ChildValue::Class(class)) => {
                                derives.contains(&(name.clone(), class.clone()))
                            }
                            (GrammarSymbol::LexemeKind(_), ChildValue::Class(_)) => false,
                            (GrammarSymbol::LexemeKind(_), _) => true,
                            (GrammarSymbol::Nonterminal(_), _) => false,
                        }
                    });
                    if reachable {
                        changed |= derives.insert((nonterminal.clone(), node.class.clone()));
                    }
                }
            }
        }
    }
    derives
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{Lexeme, Production};

    const ARITH: &str = "(datatype Ast (Num i64) (Add Ast Ast))";

    fn num(n: i64) -> Ast {
        Ast::constructor("Num", vec![Ast::Number(n)])
    }

    fn add(left: Ast, right: Ast) -> Ast {
        Ast::constructor("Add", vec![left, right])
    }

    fn arithmetic() -> Grammar {
        Grammar::new(
            "Expr",
            vec![
                Production {
                    nonterminal: "Expr".into(),
                    symbols: vec![GrammarSymbol::LexemeKind("number".into())],
                    constructor: "Num".into(),
                    selected_positions: vec![1],
                },
                Production {
                    nonterminal: "Expr".into(),
                    symbols: vec![
                        GrammarSymbol::LexemeKind("(".into()),
                        GrammarSymbol::Nonterminal("Expr".into()),
                        GrammarSymbol::LexemeKind("+".into()),
                        GrammarSymbol::Nonterminal("Expr".into()),
                        GrammarSymbol::LexemeKind(")".into()),
                    ],
                    constructor: "Add".into(),
                    selected_positions: vec![2, 4],
                },
            ],
        )
        .unwrap()
    }

    fn with_root(root: &Ast) -> EGraph {
        let mut egraph = EGraph::new(ARITH).unwrap();
        egraph.insert_ast(root).unwrap();
        egraph
    }

    fn predict(hole: HoleId, production: ProductionId, child_holes: Vec<HoleId>) -> PatternStep {
        PatternStep::Predict {
            hole,
            production,
            child_holes,
        }
    }

    fn read_number(hole: HoleId, n: i64) -> PatternStep {
        PatternStep::Read {
            hole,
            lexeme: Lexeme::number("number", n),
        }
    }

    #[test]
    fn derives_relation_covers_root_and_leaves() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        let derives = derives_relation(&egraph, &grammar);
        let root_class = egraph.class_of(&root).unwrap();
        let one_class = egraph.class_of(&num(1)).unwrap();
        assert!(derives.contains(&("Expr".into(), root_class)));
        assert!(derives.contains(&("Expr".into(), one_class)));
        assert_eq!(derives.len(), 3);
    }

    #[test]
    fn fresh_matcher_is_realizable_iff_root_is_derivable() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        assert!(Matcher::new(root, &egraph, &grammar).realizable());
    }

    #[test]
    fn predict_and_reads_narrow_to_the_answer() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root, &egraph, &grammar);
        matcher.advance(&egraph, &grammar, &[predict(0, 1, vec![1, 2])]);
        assert!(matcher.realizable());
        matcher.advance(
            &egraph,
            &grammar,
            &[predict(1, 0, vec![3]), read_number(3, 2)],
        );
        assert!(!matcher.realizable());
    }

    #[test]
    fn completions_are_reported_with_references() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root.clone(), &egraph, &grammar);
        let completed = matcher.advance(
            &egraph,
            &grammar,
            &[predict(0, 0, vec![1]), read_number(1, 1)],
        );
        assert_eq!(
            completed,
            vec![CompletedNode {
                hole: 0,
                constructor: "Num".into(),
                children: vec![InsertRef::Number(1)],
            }]
        );
    }

    #[test]
    fn refresh_recovers_realizability_after_growth() {
        let root = add(num(1), num(2));
        let mut egraph = with_root(&root);
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root, &egraph, &grammar);
        matcher.advance(
            &egraph,
            &grammar,
            &[
                predict(0, 1, vec![1, 2]),
                predict(1, 0, vec![3]),
                read_number(3, 2),
            ],
        );
        assert!(!matcher.realizable());
        egraph
            .run_program("(rewrite (Add x y) (Add y x))\n(run 5)")
            .unwrap();
        matcher.refresh(&egraph, &grammar);
        assert!(matcher.realizable());
    }

    #[test]
    fn completing_a_child_re_narrows_open_siblings() {
        // Root class holds Add(1,2) and Add(4,5): once the first argument is
        // read as 1, the second argument's candidates must shrink to {2}.
        let root = add(num(1), num(2));
        let mut egraph = with_root(&root);
        egraph.insert_ast(&num(4)).unwrap();
        egraph.insert_ast(&num(5)).unwrap();
        egraph
            .run_program("(union (Add (Num 1) (Num 2)) (Add (Num 4) (Num 5)))")
            .unwrap();
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root, &egraph, &grammar);
        matcher.advance(
            &egraph,
            &grammar,
            &[
                predict(0, 1, vec![1, 2]),
                predict(1, 0, vec![3]),
                read_number(3, 1),
            ],
        );
        assert!(matcher.realizable());
        // Predicting the sibling as the number 5 must already be doomed,
        // before the sibling's subtree completes.
        matcher.advance(&egraph, &grammar, &[predict(2, 0, vec![4])]);
        matcher.advance(&egraph, &grammar, &[read_number(4, 5)]);
        assert!(!matcher.realizable());
    }
}
