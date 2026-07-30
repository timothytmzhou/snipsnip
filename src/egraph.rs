use crate::ast::Ast;
use egglog::{Read, Core};

/// Canonical identifier of an e-class, stable between rule runs.
pub type ClassId = String;

/// A child of an e-node: an e-class or a primitive value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChildValue {
    Class(ClassId),
    Number(i64),
    Text(String),
}

/// One e-node: `constructor(children) -> class`.
#[derive(Debug, Clone)]
pub struct ENode {
    pub children: Vec<ChildValue>,
    pub class: ClassId,
}

#[derive(Debug)]
pub struct EGraphError(pub String);

/// A live egglog engine; every query reads the current e-graph directly.
pub struct EGraph {
    engine: egglog::EGraph,
    inserted: u64,
}

impl EGraph {
    /// Loads an egglog program (datatypes and rules).
    pub fn new(program: &str) -> Result<EGraph, EGraphError> {
        let mut engine = egglog::EGraph::default();
        engine
            .parse_and_run_program(None, program)
            .map_err(|e| EGraphError(e.to_string()))?;
        Ok(EGraph {
            engine,
            inserted: 0,
        })
    }

    /// Runs egglog commands against the live engine.
    pub fn run_program(&mut self, program: &str) -> Result<(), EGraphError> {
        self.engine
            .parse_and_run_program(None, program)
            .map_err(|e| EGraphError(e.to_string()))?;
        Ok(())
    }

    /// Inserts a ground tree so future rule runs can involve it.
    pub fn insert_ast(&mut self, ast: &Ast) -> Result<(), EGraphError> {
        self.inserted += 1;
        let binding = format!("(let __inserted_{} {})", self.inserted, ast.to_egglog());
        self.run_program(&binding)
    }

    /// The e-class of a ground tree, if it is represented; never inserts.
    pub fn class_of(&self, ast: &Ast) -> Option<ClassId> {
        self.engine.read(|state| Self::evaluate(&state, ast))
    }

    /// E-nodes of one constructor whose class is `class`.
    pub fn nodes_in_class(&self, constructor: &str, class: &ClassId) -> Vec<ENode> {
        self.all_nodes(constructor)
            .into_iter()
            .filter(|node| &node.class == class)
            .collect()
    }

    /// All e-nodes of one constructor.
    pub fn nodes_of_constructor(&self, constructor: &str) -> Vec<ENode> {
        self.all_nodes(constructor)
    }

    fn evaluate(state: &egglog::ReadState<'_, '_>, ast: &Ast) -> Option<ClassId> {
        Self::evaluate_to_value(state, ast).map(|value| class_id(value))
    }

    fn evaluate_to_value(
        state: &egglog::ReadState<'_, '_>,
        ast: &Ast,
    ) -> Option<egglog::Value> {
        match ast {
            Ast::Number(n) => Some(state.base_to_value::<i64>(*n)),
            Ast::Text(s) => Some(state.base_to_value::<String>(s.clone())),
            Ast::Constructor { name, children } => {
                let mut child_values = Vec::with_capacity(children.len());
                for child in children {
                    child_values.push(Self::evaluate_to_value(state, child)?);
                }
                state
                    .eclass_of(name, egglog::RawValues(child_values))
                    .ok()
                    .flatten()
            }
        }
    }

    fn all_nodes(&self, constructor: &str) -> Vec<ENode> {
        let input_sorts = self.input_sorts(constructor);
        let Some(input_sorts) = input_sorts else {
            return Vec::new();
        };
        let mut nodes = Vec::new();
        let _ = self.engine.read(|state| {
            let _ = state.constructor_enodes(constructor, |enode| {
                let children = enode
                    .children
                    .iter()
                    .zip(&input_sorts)
                    .map(|(&value, is_class)| {
                        if *is_class {
                            ChildValue::Class(class_id(value))
                        } else {
                            ChildValue::Number(state.value_to_base::<i64>(value))
                        }
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

    /// For each input column of the constructor: is it an e-class column?
    fn input_sorts(&self, constructor: &str) -> Option<Vec<bool>> {
        let function = self
            .engine
            .functions_iter()
            .find(|(name, _)| name.as_str() == constructor)?
            .1;
        Some(
            function
                .schema()
                .input
                .iter()
                .map(|sort| sort.is_eq_sort())
                .collect(),
        )
    }
}

fn class_id(value: egglog::Value) -> ClassId {
    format!("{value:?}")
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
    fn bad_programs_are_errors() {
        assert!(EGraph::new("(nonsense").is_err());
        let mut egraph = with_root();
        assert!(egraph.run_program("(check (= (Num 1) (Num 2)))").is_err());
    }
}
