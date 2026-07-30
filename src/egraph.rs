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

/// A remembered insertion: its row in the keyed table and its class value.
struct Insertion {
    table: String,
    row: i64,
    value: egglog::Value,
}

/// The loaded schema of a function: input columns and output sort.
struct Signature {
    columns: Option<Vec<Column>>,
    output: String,
}

/// A live egglog engine plus an e-node index by (constructor, class),
/// rebuilt when rules run and extended incrementally on inserts.
pub struct EGraph {
    engine: egglog::EGraph,
    inserted: i64,
    named: HashMap<u64, Insertion>,
    tables: HashMap<String, String>,
    signatures: HashMap<String, Signature>,
    nodes_by_class: HashMap<String, HashMap<ClassId, Vec<ENode>>>,
    nodes_by_constructor: HashMap<String, Vec<ENode>>,
    known_nodes: HashMap<String, HashSet<Vec<ChildValue>>>,
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
            tables: HashMap::new(),
            signatures: HashMap::new(),
            nodes_by_class: HashMap::new(),
            nodes_by_constructor: HashMap::new(),
            known_nodes: HashMap::new(),
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

    /// Runs the loaded rules for `iterations`; true if the e-graph changed,
    /// in which case the index is rebuilt.
    pub fn saturate(&mut self, iterations: u32) -> Result<bool, Error> {
        let outputs = self
            .engine
            .parse_and_run_program(None, &format!("(run {iterations})"))
            .map_err(|e| Error::EGraph(e.to_string()))?;
        let changed = outputs.iter().any(|output| match output {
            egglog::CommandOutput::RunSchedule(report) => report.updated,
            _ => false,
        });
        if changed {
            self.rebuild_index();
        }
        Ok(changed)
    }

    /// Inserts a ground tree so future rule runs can involve it; leaves alone
    /// add nothing. One shallow command per node, so depth is unbounded.
    pub fn insert_ast(&mut self, ast: &Ast) -> Result<(), Error> {
        enum Task<'a> {
            Visit(&'a Ast),
            Build(&'a str, usize),
        }
        enum Planned {
            Row(i64, String),
            Number(i64),
            Text(String),
        }
        if !matches!(ast, Ast::Constructor { .. }) {
            return Ok(());
        }
        let mut plan: Vec<(String, i64, String, Vec<Planned>)> = Vec::new();
        let mut results: Vec<Planned> = Vec::new();
        let mut tasks = vec![Task::Visit(ast)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Ast::Number(n)) => results.push(Planned::Number(*n)),
                Task::Visit(Ast::Text(s)) => results.push(Planned::Text(s.clone())),
                Task::Visit(Ast::Constructor { name, children }) => {
                    tasks.push(Task::Build(name, children.len()));
                    for child in children.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                }
                Task::Build(name, arity) => {
                    let children = results.split_off(results.len() - arity);
                    let table = self.table_for(name)?;
                    self.inserted += 1;
                    let row = self.inserted;
                    plan.push((table.clone(), row, name.to_string(), children));
                    results.push(Planned::Row(row, table));
                }
            }
        }
        let mut program = String::new();
        for (table, row, constructor, children) in &plan {
            program.push_str(&format!("(set ({table} {row}) ({constructor}"));
            for child in children {
                program.push(' ');
                match child {
                    Planned::Row(child_row, child_table) => {
                        program.push_str(&format!("({child_table} {child_row})"))
                    }
                    Planned::Number(n) => program.push_str(&n.to_string()),
                    Planned::Text(s) => program.push_str(&Ast::Text(s.clone()).to_egglog()),
                }
            }
            program.push_str("))\n");
        }
        self.engine
            .parse_and_run_program(None, &program)
            .map_err(|e| Error::EGraph(e.to_string()))?;
        let mut classes: HashMap<i64, egglog::Value> = HashMap::new();
        self.engine.read(|state| {
            for (table, row, _, _) in &plan {
                let row_value = state.base_to_value::<i64>(*row);
                if let Ok(Some(value)) =
                    state.lookup(table.as_str(), egglog::RawValues(vec![row_value]))
                {
                    classes.insert(*row, value);
                }
            }
        });
        if classes.len() != plan.len() {
            return Err(Error::EGraph("inserted tree not found".to_string()));
        }
        for (_, row, constructor, children) in plan {
            let children = children
                .into_iter()
                .map(|child| match child {
                    Planned::Row(child_row, _) => ChildValue::Class(class_id(classes[&child_row])),
                    Planned::Number(n) => ChildValue::Number(n),
                    Planned::Text(s) => ChildValue::Text(s),
                })
                .collect();
            let class = class_id(classes[&row]);
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
        let table = self.table_for(constructor)?;
        self.inserted += 1;
        let row = self.inserted;
        let mut command = format!("(set ({table} {row}) ({constructor}");
        let mut child_values = Vec::with_capacity(children.len());
        for child in children {
            command.push(' ');
            match child {
                InsertRef::Node(child_key) => match self.named.get(child_key) {
                    Some(insertion) => {
                        command.push_str(&format!("({} {})", insertion.table, insertion.row));
                        child_values.push(ChildValue::Class(class_id(insertion.value)));
                    }
                    None => return Err(Error::EGraph(format!("unknown insertion {child_key}"))),
                },
                InsertRef::Number(n) => {
                    command.push_str(&n.to_string());
                    child_values.push(ChildValue::Number(*n));
                }
                InsertRef::Text(s) => {
                    command.push_str(&Ast::Text(s.clone()).to_egglog());
                    child_values.push(ChildValue::Text(s.clone()));
                }
            }
        }
        command.push_str("))");
        self.engine
            .parse_and_run_program(None, &command)
            .map_err(|e| Error::EGraph(e.to_string()))?;
        let class_value = self.engine.read(|state| {
            let row_value = state.base_to_value::<i64>(row);
            state
                .lookup(table.as_str(), egglog::RawValues(vec![row_value]))
                .ok()
                .flatten()
        });
        let Some(class_value) = class_value else {
            return Err(Error::EGraph(format!(
                "insertion of {constructor} not found"
            )));
        };
        self.named.insert(
            key,
            Insertion {
                table,
                row,
                value: class_value,
            },
        );
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
                .read(|state| tree_value(&state, ast).map(class_id)),
            _ => None,
        }
    }

    /// E-nodes of one constructor whose class is `class`.
    pub fn nodes_in_class(&self, constructor: &str, class: &ClassId) -> &[ENode] {
        self.nodes_by_class
            .get(constructor)
            .and_then(|by_class| by_class.get(class))
            .map_or(&[], Vec::as_slice)
    }

    /// All e-nodes of one constructor.
    pub fn nodes_of_constructor(&self, constructor: &str) -> &[ENode] {
        self.nodes_by_constructor
            .get(constructor)
            .map_or(&[], Vec::as_slice)
    }

    /// The number of children of a constructor, if it is loaded and supported.
    pub fn constructor_arity(&self, constructor: &str) -> Option<usize> {
        self.signatures
            .get(constructor)?
            .columns
            .as_ref()
            .map(Vec::len)
    }

    /// The keyed table holding insertions of the constructor's sort,
    /// declared on first use.
    fn table_for(&mut self, constructor: &str) -> Result<String, Error> {
        let sort = self
            .signatures
            .get(constructor)
            .map(|signature| signature.output.clone())
            .ok_or_else(|| {
                Error::EGraph(format!("unknown or unsupported constructor {constructor}"))
            })?;
        if let Some(table) = self.tables.get(&sort) {
            return Ok(table.clone());
        }
        let table = format!("__nodes_{sort}");
        self.engine
            .parse_and_run_program(None, &format!("(function {table} (i64) {sort} :no-merge)"))
            .map_err(|e| Error::EGraph(e.to_string()))?;
        self.tables.insert(sort, table.clone());
        Ok(table)
    }

    /// Rebuilds the schema cache and the whole index, and re-canonicalizes
    /// remembered insertions.
    fn rebuild_index(&mut self) {
        self.nodes_by_class.clear();
        self.nodes_by_constructor.clear();
        self.known_nodes.clear();
        self.signatures.clear();
        let mut enumerable = Vec::new();
        for (name, function) in self.engine.functions_iter() {
            let schema = function.schema();
            let columns = schema
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
                .collect();
            self.signatures.insert(
                name.clone(),
                Signature {
                    columns,
                    output: schema.output.name().to_string(),
                },
            );
            let internal = self.tables.values().any(|table| table == name);
            if !function.is_let_binding() && !internal {
                enumerable.push(name.clone());
            }
        }
        for name in enumerable {
            for node in self.all_nodes(&name) {
                self.add_to_index(&name, node);
            }
        }
        let mut refreshed = HashMap::new();
        self.engine.read(|state| {
            for (key, insertion) in &self.named {
                let row_value = state.base_to_value::<i64>(insertion.row);
                if let Ok(Some(value)) =
                    state.lookup(insertion.table.as_str(), egglog::RawValues(vec![row_value]))
                {
                    refreshed.insert(
                        *key,
                        Insertion {
                            table: insertion.table.clone(),
                            row: insertion.row,
                            value,
                        },
                    );
                }
            }
        });
        self.named = refreshed;
    }

    fn add_to_index(&mut self, constructor: &str, node: ENode) {
        let known = self.known_nodes.entry(constructor.to_string()).or_default();
        if !known.insert(node.children.clone()) {
            return;
        }
        self.nodes_by_class
            .entry(constructor.to_string())
            .or_default()
            .entry(node.class.clone())
            .or_default()
            .push(node.clone());
        self.nodes_by_constructor
            .entry(constructor.to_string())
            .or_default()
            .push(node);
    }

    fn all_nodes(&self, constructor: &str) -> Vec<ENode> {
        let Some(columns) = self
            .signatures
            .get(constructor)
            .and_then(|signature| signature.columns.as_ref())
        else {
            return Vec::new();
        };
        let mut nodes = Vec::new();
        self.engine.read(|state| {
            let _ = state.constructor_enodes(constructor, |enode| {
                let children = enode
                    .children
                    .iter()
                    .zip(columns)
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

/// The engine value of a ground tree, by iterative bottom-up lookup.
fn tree_value(state: &egglog::ReadState<'_, '_>, ast: &Ast) -> Option<egglog::Value> {
    enum Task<'a> {
        Visit(&'a Ast),
        Build(&'a str, usize),
    }
    let mut values: Vec<egglog::Value> = Vec::new();
    let mut tasks = vec![Task::Visit(ast)];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Ast::Number(n)) => values.push(state.base_to_value::<i64>(*n)),
            Task::Visit(Ast::Text(s)) => {
                values.push(state.base_to_value::<egglog::sort::S>(s.clone().into()))
            }
            Task::Visit(Ast::Constructor { name, children }) => {
                tasks.push(Task::Build(name, children.len()));
                for child in children.iter().rev() {
                    tasks.push(Task::Visit(child));
                }
            }
            Task::Build(name, arity) => {
                let child_values = values.split_off(values.len() - arity);
                values.push(
                    state
                        .eclass_of(name, egglog::RawValues(child_values))
                        .ok()
                        .flatten()?,
                );
            }
        }
    }
    values.pop()
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
    fn saturate_reports_change_then_quiescence() {
        let mut egraph = with_root();
        egraph
            .run_program("(rewrite (Add x y) (Add y x))")
            .unwrap();
        assert!(egraph.saturate(5).unwrap());
        assert!(!egraph.saturate(5).unwrap());
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
    fn insertions_survive_unions_and_rule_runs() {
        let mut egraph = with_root();
        egraph
            .insert_node(1, "Num", &[InsertRef::Number(3)])
            .unwrap();
        egraph.run_program("(union (Num 3) (Num 1))").unwrap();
        egraph
            .insert_node(2, "Add", &[InsertRef::Node(1), InsertRef::Node(1)])
            .unwrap();
        assert_eq!(
            egraph.class_of(&add(num(3), num(3))),
            egraph.class_of(&add(num(1), num(1)))
        );
    }

    #[test]
    fn deep_trees_do_not_overflow_the_stack() {
        let mut egraph = EGraph::new(ARITH).unwrap();
        let mut tree = num(5000);
        for i in (0..5000).rev() {
            tree = add(num(i), tree);
        }
        egraph.insert_ast(&tree).unwrap();
        assert!(egraph.class_of(&tree).is_some());
        assert_eq!(tree.to_egglog().matches("(Add").count(), 5000);
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
