use crate::ast::Ast;
use crate::Error;
use egglog::{Core, Read};
use std::collections::{HashMap, HashSet};

/// Canonical identifier of an e-class, stable between rule runs.
pub type ClassId = String;

/// A child of an e-node: an e-class or a primitive value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChildValue {
    Class(ClassId),
    Number(i64),
    Text(String),
}

/// A child of a tree being inserted: an earlier insertion or a leaf value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InsertRef {
    Node(u64),
    Number(i64),
    Text(String),
}

/// One e-node: `constructor(children) -> class`.
#[derive(Debug, Clone)]
pub struct ENode {
    pub children: Vec<ChildValue>,
    pub class: ClassId,
}

/// A live egglog engine plus an e-node index by (constructor, class),
/// rebuilt when rules run and extended incrementally on inserts.
pub struct EGraph {
    engine: egglog::EGraph,
    inserted: u64,
    named: HashMap<u64, (String, egglog::Value)>,
    nodes_by_class: HashMap<(String, ClassId), Vec<ENode>>,
    nodes_by_constructor: HashMap<String, Vec<ENode>>,
    known_nodes: HashSet<(String, Vec<ChildValue>)>,
}

impl EGraph {
    /// Loads an egglog program (datatypes and rules).
    pub fn new(program: &str) -> Result<EGraph, Error> {
        let mut engine = egglog::EGraph::default();
        engine
            .parse_and_run_program(None, program)
            .map_err(|e| Error::EGraph(e.to_string()))?;
        let mut egraph = EGraph {
            engine,
            inserted: 0,
            named: HashMap::new(),
            nodes_by_class: HashMap::new(),
            nodes_by_constructor: HashMap::new(),
            known_nodes: HashSet::new(),
        };
        egraph.rebuild_index();
        Ok(egraph)
    }

    /// Runs egglog commands and rebuilds the index (rules may merge classes).
    pub fn run_program(&mut self, program: &str) -> Result<(), Error> {
        self.engine
            .parse_and_run_program(None, program)
            .map_err(|e| Error::EGraph(e.to_string()))?;
        self.rebuild_index();
        Ok(())
    }

    /// Inserts a ground tree so future rule runs can involve it.
    pub fn insert_ast(&mut self, ast: &Ast) -> Result<(), Error> {
        self.inserted += 1;
        let binding = format!("(let __tree_{} {})", self.inserted, ast.to_egglog());
        self.engine
            .parse_and_run_program(None, &binding)
            .map_err(|e| Error::EGraph(e.to_string()))?;
        let mut entries = Vec::new();
        self.engine.read(|state| {
            collect_tree_nodes(&state, ast, &mut entries);
        });
        for (constructor, children, class) in entries {
            self.add_to_index(&constructor, ENode { children, class });
        }
        Ok(())
    }

    /// Inserts one constructor application whose children are earlier
    /// insertions (by key) or leaf values; cost is linear in the arity.
    pub fn insert_node(
        &mut self,
        key: u64,
        constructor: &str,
        children: &[InsertRef],
    ) -> Result<(), Error> {
        let name = format!("__node_{key}");
        let mut rendered = format!("(let {name} ({constructor}");
        for child in children {
            rendered.push(' ');
            match child {
                InsertRef::Node(child_key) => match self.named.get(child_key) {
                    Some((child_name, _)) => rendered.push_str(child_name),
                    None => return Err(Error::EGraph(format!("unknown insertion {child_key}"))),
                },
                InsertRef::Number(n) => rendered.push_str(&Ast::Number(*n).to_egglog()),
                InsertRef::Text(s) => rendered.push_str(&Ast::Text(s.clone()).to_egglog()),
            }
        }
        rendered.push_str("))");
        self.engine
            .parse_and_run_program(None, &rendered)
            .map_err(|e| Error::EGraph(e.to_string()))?;
        let (child_values, class_value) = self.engine.read(|state| {
            let values: Vec<egglog::Value> = children
                .iter()
                .map(|child| match child {
                    InsertRef::Node(child_key) => self.named[child_key].1,
                    InsertRef::Number(n) => state.base_to_value::<i64>(*n),
                    InsertRef::Text(s) => {
                        state.base_to_value::<egglog::sort::S>(s.clone().into())
                    }
                })
                .collect();
            let child_values: Vec<ChildValue> = children
                .iter()
                .map(|child| match child {
                    InsertRef::Node(child_key) => {
                        ChildValue::Class(class_id(self.named[child_key].1))
                    }
                    InsertRef::Number(n) => ChildValue::Number(*n),
                    InsertRef::Text(s) => ChildValue::Text(s.clone()),
                })
                .collect();
            let class_value = state
                .eclass_of(constructor, egglog::RawValues(values))
                .ok()
                .flatten();
            (child_values, class_value)
        });
        let Some(class_value) = class_value else {
            return Err(Error::EGraph(format!(
                "insertion of {constructor} not found"
            )));
        };
        self.named.insert(key, (name, class_value));
        let node = ENode {
            children: child_values,
            class: class_id(class_value),
        };
        self.add_to_index(constructor, node);
        Ok(())
    }

    /// The e-class of a ground constructor tree, if it is represented;
    /// leaves have no e-class. Never inserts.
    pub fn class_of(&self, ast: &Ast) -> Option<ClassId> {
        match ast {
            Ast::Constructor { .. } => self
                .engine
                .read(|state| evaluate_to_value(&state, ast).map(class_id)),
            _ => None,
        }
    }

    /// E-nodes of one constructor whose class is `class`.
    pub fn nodes_in_class(&self, constructor: &str, class: &ClassId) -> Vec<ENode> {
        self.nodes_by_class
            .get(&(constructor.to_string(), class.clone()))
            .cloned()
            .unwrap_or_default()
    }

    /// All e-nodes of one constructor.
    pub fn nodes_of_constructor(&self, constructor: &str) -> Vec<ENode> {
        self.nodes_by_constructor
            .get(constructor)
            .cloned()
            .unwrap_or_default()
    }

    /// The number of children of a constructor, if it is loaded and supported.
    pub fn constructor_arity(&self, constructor: &str) -> Option<usize> {
        self.input_columns(constructor).map(|columns| columns.len())
    }

    /// Rebuilds the whole index and re-canonicalizes remembered insertions.
    fn rebuild_index(&mut self) {
        self.nodes_by_class.clear();
        self.nodes_by_constructor.clear();
        self.known_nodes.clear();
        let names: Vec<String> = self
            .engine
            .functions_iter()
            .filter(|(_, function)| !function.is_let_binding())
            .map(|(name, _)| name.clone())
            .collect();
        for name in names {
            for node in self.all_nodes(&name) {
                self.add_to_index(&name, node);
            }
        }
        let mut refreshed = HashMap::new();
        self.engine.read(|state| {
            for (key, (name, _)) in &self.named {
                if let Ok(Some(value)) = state.lookup(name.as_str(), egglog::RawValues(vec![])) {
                    refreshed.insert(*key, (name.clone(), value));
                }
            }
        });
        self.named = refreshed;
    }

    fn add_to_index(&mut self, constructor: &str, node: ENode) {
        if !self
            .known_nodes
            .insert((constructor.to_string(), node.children.clone()))
        {
            return;
        }
        self.nodes_by_class
            .entry((constructor.to_string(), node.class.clone()))
            .or_default()
            .push(node.clone());
        self.nodes_by_constructor
            .entry(constructor.to_string())
            .or_default()
            .push(node);
    }

    fn all_nodes(&self, constructor: &str) -> Vec<ENode> {
        let Some(columns) = self.input_columns(constructor) else {
            return Vec::new();
        };
        let mut nodes = Vec::new();
        let _ = self.engine.read(|state| {
            let _ = state.constructor_enodes(constructor, |enode| {
                let children = enode
                    .children
                    .iter()
                    .zip(&columns)
                    .map(|(&value, column)| match column {
                        Column::Class => ChildValue::Class(class_id(value)),
                        Column::Number => ChildValue::Number(state.value_to_base::<i64>(value)),
                        Column::Text => ChildValue::Text(
                            state.value_to_base::<egglog::sort::S>(value).to_string(),
                        ),
                    })
                    .collect();
                nodes.push(ENode {
                    children,
                    class: class_id(enode.eclass),
                });
            });
        });
        nodes
    }

    /// The kind of each input column, or None if any column is unsupported.
    fn input_columns(&self, constructor: &str) -> Option<Vec<Column>> {
        let function = self
            .engine
            .functions_iter()
            .find(|(name, _)| name.as_str() == constructor)?
            .1;
        function
            .schema()
            .input
            .iter()
            .map(|sort| {
                if sort.is_eq_sort() {
                    Some(Column::Class)
                } else if sort.name() == "i64" {
                    Some(Column::Number)
                } else if sort.name() == "String" {
                    Some(Column::Text)
                } else {
                    None
                }
            })
            .collect()
    }
}

/// The kind of one e-node input column.
enum Column {
    Class,
    Number,
    Text,
}

fn class_id(value: egglog::Value) -> ClassId {
    format!("{value:?}")
}

/// The engine value of a ground tree, by bottom-up lookup.
fn evaluate_to_value(state: &egglog::ReadState<'_, '_>, ast: &Ast) -> Option<egglog::Value> {
    match ast {
        Ast::Number(n) => Some(state.base_to_value::<i64>(*n)),
        Ast::Text(s) => Some(state.base_to_value::<egglog::sort::S>(s.clone().into())),
        Ast::Constructor { name, children } => {
            let mut child_values = Vec::with_capacity(children.len());
            for child in children {
                child_values.push(evaluate_to_value(state, child)?);
            }
            state
                .eclass_of(name, egglog::RawValues(child_values))
                .ok()
                .flatten()
        }
    }
}

/// Bottom-up over the tree: record each constructor node and return its
/// engine value and its indexable child form.
fn collect_tree_nodes(
    state: &egglog::ReadState<'_, '_>,
    ast: &Ast,
    entries: &mut Vec<(String, Vec<ChildValue>, ClassId)>,
) -> Option<(egglog::Value, ChildValue)> {
    match ast {
        Ast::Number(n) => Some((state.base_to_value::<i64>(*n), ChildValue::Number(*n))),
        Ast::Text(s) => Some((
            state.base_to_value::<egglog::sort::S>(s.clone().into()),
            ChildValue::Text(s.clone()),
        )),
        Ast::Constructor { name, children } => {
            let mut values = Vec::with_capacity(children.len());
            let mut child_values = Vec::with_capacity(children.len());
            for child in children {
                let (value, child_value) = collect_tree_nodes(state, child, entries)?;
                values.push(value);
                child_values.push(child_value);
            }
            let class = state
                .eclass_of(name, egglog::RawValues(values))
                .ok()
                .flatten()?;
            entries.push((name.clone(), child_values, class_id(class)));
            Some((class, ChildValue::Class(class_id(class))))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ARITH: &str = "(datatype Ast (Num i64) (Add Ast Ast))";

    fn num(n: i64) -> Ast {
        Ast::constructor("Num", vec![Ast::Number(n)])
    }

    fn add(left: Ast, right: Ast) -> Ast {
        Ast::constructor("Add", vec![left, right])
    }

    fn with_root() -> EGraph {
        let mut egraph = EGraph::new(ARITH).unwrap();
        egraph.insert_ast(&add(num(1), num(2))).unwrap();
        egraph
    }

    #[test]
    fn class_of_finds_inserted_trees_and_nothing_else() {
        let egraph = with_root();
        assert!(egraph.class_of(&num(1)).is_some());
        assert!(egraph.class_of(&add(num(1), num(2))).is_some());
        assert!(egraph.class_of(&num(9)).is_none());
        assert!(egraph.class_of(&add(num(2), num(1))).is_none());
    }

    #[test]
    fn leaves_have_no_class() {
        let egraph = with_root();
        assert!(egraph.class_of(&Ast::Number(1)).is_none());
        assert!(egraph.class_of(&Ast::Text("1".into())).is_none());
    }

    #[test]
    fn distinct_trees_get_distinct_classes() {
        let mut egraph = with_root();
        egraph.insert_ast(&num(9)).unwrap();
        assert_ne!(egraph.class_of(&num(1)), egraph.class_of(&num(9)));
    }

    #[test]
    fn nodes_are_enumerable_by_constructor_and_class() {
        let egraph = with_root();
        let root_class = egraph.class_of(&add(num(1), num(2))).unwrap();
        let one_class = egraph.class_of(&num(1)).unwrap();
        let adds = egraph.nodes_of_constructor("Add");
        assert_eq!(adds.len(), 1);
        assert_eq!(adds[0].children[0], ChildValue::Class(one_class));
        let in_root = egraph.nodes_in_class("Add", &root_class);
        assert_eq!(in_root.len(), 1);
        assert!(egraph.nodes_of_constructor("Missing").is_empty());
    }

    #[test]
    fn number_children_are_primitive_values() {
        let egraph = with_root();
        let nums = egraph.nodes_of_constructor("Num");
        assert_eq!(nums.len(), 2);
        assert!(nums
            .iter()
            .all(|node| matches!(node.children[0], ChildValue::Number(_))));
    }

    #[test]
    fn rules_add_nodes_and_keep_classes() {
        let mut egraph = with_root();
        let root_class = egraph.class_of(&add(num(1), num(2))).unwrap();
        egraph
            .run_program("(rewrite (Add x y) (Add y x))\n(run 5)")
            .unwrap();
        assert_eq!(egraph.nodes_in_class("Add", &root_class).len(), 2);
        assert_eq!(egraph.class_of(&add(num(2), num(1))), Some(root_class));
    }

    #[test]
    fn insertions_by_reference_match_whole_trees() {
        let mut egraph = with_root();
        egraph
            .insert_node(1, "Num", &[InsertRef::Number(3)])
            .unwrap();
        egraph
            .insert_node(2, "Add", &[InsertRef::Node(1), InsertRef::Node(1)])
            .unwrap();
        assert!(egraph.class_of(&add(num(3), num(3))).is_some());
        let three_class = egraph.class_of(&num(3)).unwrap();
        assert!(!egraph.nodes_in_class("Num", &three_class).is_empty());
    }

    #[test]
    fn arity_is_reported() {
        let egraph = with_root();
        assert_eq!(egraph.constructor_arity("Add"), Some(2));
        assert_eq!(egraph.constructor_arity("Num"), Some(1));
        assert_eq!(egraph.constructor_arity("Missing"), None);
    }

    #[test]
    fn bad_programs_are_errors() {
        assert!(EGraph::new("(nonsense").is_err());
        let mut egraph = with_root();
        assert!(egraph.run_program("(check (= (Num 1) (Num 2)))").is_err());
    }
}
