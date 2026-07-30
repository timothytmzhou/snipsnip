use crate::ast::Ast;
use crate::egraph::{ChildValue, ClassId, EGraph, ENode};
use crate::grammar::{Grammar, GrammarSymbol, LexemeValue, ProductionId};
use crate::parser::{HoleId, PatternStep};
use std::collections::{HashMap, HashSet};

/// Decides, incrementally, whether the prefix pattern has a completion
/// equal to the root tree; holes are constrained by their grammar sorts.
pub struct Matcher {
    root: Ast,
    steps: Vec<PatternStep>,
    completed: Vec<Ast>,
    state: State,
}

/// Everything derived from the current e-graph; rebuilt by `refresh`.
struct State {
    root_class: Option<ClassId>,
    derivable: HashSet<(String, ClassId)>,
    holes: HashMap<HoleId, Hole>,
    nodes: HashMap<HoleId, BuildingNode>,
    feasible: bool,
}

/// Where a hole or node hangs: under which node, at which child index.
type Parent = Option<(HoleId, usize)>;

/// An open hole and the e-classes its subtree may land in.
struct Hole {
    allowed_classes: HashSet<ClassId>,
    parent: Parent,
}

/// A predicted constructor with children still being filled, keyed by the
/// hole it replaced; `surviving` are the e-nodes still compatible.
struct BuildingNode {
    constructor: String,
    child_slots: Vec<Slot>,
    parent: Parent,
    surviving: Vec<ENode>,
}

enum Slot {
    Open,
    Done(Ast),
}

impl Matcher {
    /// A matcher for the query (start hole 0, root tree).
    pub fn new(root: Ast, egraph: &EGraph, grammar: &Grammar) -> Matcher {
        let mut matcher = Matcher {
            root,
            steps: Vec::new(),
            completed: Vec::new(),
            state: State::empty(),
        };
        matcher.refresh(egraph, grammar);
        matcher
    }

    /// Applies one pattern step.
    pub fn issue(&mut self, egraph: &EGraph, grammar: &Grammar, step: &PatternStep) {
        self.steps.push(step.clone());
        self.state.apply(egraph, grammar, step, &mut self.completed);
    }

    /// Trees that became fully concrete since the last call.
    pub fn take_completed(&mut self) -> Vec<Ast> {
        std::mem::take(&mut self.completed)
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
    pub fn nonempty(&self) -> bool {
        self.state.feasible
    }
}

impl State {
    fn empty() -> State {
        State {
            root_class: None,
            derivable: HashSet::new(),
            holes: HashMap::new(),
            nodes: HashMap::new(),
            feasible: false,
        }
    }

    /// Sets up the start hole against the current e-graph.
    fn begin(&mut self, egraph: &EGraph, grammar: &Grammar, root: &Ast) {
        self.root_class = egraph.class_of(root);
        self.derivable = derivable_pairs(egraph, grammar);
        let mut allowed = HashSet::new();
        if let Some(class) = &self.root_class {
            let start = grammar.start().to_string();
            if self.derivable.contains(&(start, class.clone())) {
                allowed.insert(class.clone());
            }
        }
        self.feasible = !allowed.is_empty();
        self.holes.insert(
            0,
            Hole {
                allowed_classes: allowed,
                parent: None,
            },
        );
    }

    /// Applies one step, maintaining holes, nodes, and feasibility.
    fn apply(
        &mut self,
        egraph: &EGraph,
        grammar: &Grammar,
        step: &PatternStep,
        completed: &mut Vec<Ast>,
    ) {
        match step {
            PatternStep::Predict {
                hole,
                production,
                child_holes,
            } => self.predict(egraph, grammar, *hole, *production, child_holes, completed),
            PatternStep::Read { hole, lexeme } => {
                let leaf = match &lexeme.value {
                    LexemeValue::Number(n) => Ast::Number(*n),
                    LexemeValue::Text(s) => Ast::Text(s.clone()),
                };
                let parent = self.holes.remove(hole).and_then(|h| h.parent);
                self.fill(egraph, parent, leaf, completed);
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
        completed: &mut Vec<Ast>,
    ) {
        let Some(replaced) = self.holes.remove(&hole) else {
            self.feasible = false;
            return;
        };
        let kept = kept_symbols(grammar, production);
        let constructor = grammar.production(production).constructor.clone();
        let surviving: Vec<ENode> = replaced
            .allowed_classes
            .iter()
            .flat_map(|class| egraph.nodes_in_class(&constructor, class))
            .filter(|node| self.compatible(node, &kept))
            .collect();
        if surviving.is_empty() {
            self.feasible = false;
        }
        for (index, child_hole) in child_holes.iter().enumerate() {
            let allowed_classes = surviving
                .iter()
                .filter_map(|node| match &node.children[index] {
                    ChildValue::Class(class) => Some(class.clone()),
                    _ => None,
                })
                .collect();
            self.holes.insert(
                *child_hole,
                Hole {
                    allowed_classes,
                    parent: Some((hole, index)),
                },
            );
        }
        self.nodes.insert(
            hole,
            BuildingNode {
                constructor,
                child_slots: child_holes.iter().map(|_| Slot::Open).collect(),
                parent: replaced.parent,
                surviving,
            },
        );
        if child_holes.is_empty() {
            self.complete_if_full(egraph, hole, completed);
        }
    }

    /// Every kept child of the e-node must be reachable by its grammar sort.
    fn compatible(&self, node: &ENode, kept: &[GrammarSymbol]) -> bool {
        kept.iter()
            .enumerate()
            .all(|(index, symbol)| match (symbol, &node.children[index]) {
                (GrammarSymbol::Nonterminal(name), ChildValue::Class(class)) => {
                    self.derivable.contains(&(name.clone(), class.clone()))
                }
                (GrammarSymbol::LexemeKind(_), ChildValue::Class(_)) => false,
                (GrammarSymbol::LexemeKind(_), _) => true,
                (GrammarSymbol::Nonterminal(_), _) => false,
            })
    }

    /// Puts a concrete tree at a parent slot and cascades completions upward.
    fn fill(&mut self, egraph: &EGraph, parent: Parent, tree: Ast, completed: &mut Vec<Ast>) {
        let Some((owner, index)) = parent else {
            self.finish_root(egraph, &tree);
            return;
        };
        let filled = concrete_child_value(egraph, &tree);
        let node = self.nodes.get_mut(&owner).expect("parent node exists");
        node.child_slots[index] = Slot::Done(tree);
        node.surviving
            .retain(|candidate| Some(&candidate.children[index]) == filled.as_ref());
        if node.surviving.is_empty() {
            self.feasible = false;
        }
        self.complete_if_full(egraph, owner, completed);
    }

    /// If every child of the node is concrete, build its tree and move up.
    fn complete_if_full(&mut self, egraph: &EGraph, owner: HoleId, completed: &mut Vec<Ast>) {
        let node = self.nodes.get(&owner).expect("node exists");
        let mut children = Vec::with_capacity(node.child_slots.len());
        for slot in &node.child_slots {
            match slot {
                Slot::Done(tree) => children.push(tree.clone()),
                Slot::Open => return,
            }
        }
        let constructor = node.constructor.clone();
        let parent = node.parent;
        self.nodes.remove(&owner);
        let tree = Ast::constructor(&constructor, children);
        completed.push(tree.clone());
        self.fill(egraph, parent, tree, completed);
    }

    /// The whole pattern is concrete: realizable iff it is in the root class.
    fn finish_root(&mut self, egraph: &EGraph, tree: &Ast) {
        self.feasible = match (egraph.class_of(tree), &self.root_class) {
            (Some(class), Some(root)) => &class == root,
            _ => false,
        };
    }
}

/// The symbols at a production's kept positions.
fn kept_symbols(grammar: &Grammar, production: ProductionId) -> Vec<GrammarSymbol> {
    let spec = grammar.production(production);
    spec.kept_positions
        .iter()
        .map(|position| spec.symbols[position - 1].clone())
        .collect()
}

/// A concrete tree as an e-node child value, if the tree is represented.
fn concrete_child_value(egraph: &EGraph, tree: &Ast) -> Option<ChildValue> {
    match tree {
        Ast::Number(n) => Some(ChildValue::Number(*n)),
        Ast::Text(s) => Some(ChildValue::Text(s.clone())),
        Ast::Constructor { .. } => egraph.class_of(tree).map(ChildValue::Class),
    }
}

/// All pairs (nonterminal, class) whose tree language reaches the class.
fn derivable_pairs(egraph: &EGraph, grammar: &Grammar) -> HashSet<(String, ClassId)> {
    let mut derivable: HashSet<(String, ClassId)> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for nonterminal in grammar.nonterminals() {
            for production in grammar.productions_of(&nonterminal) {
                let kept = kept_symbols(grammar, production);
                let constructor = &grammar.production(production).constructor;
                for node in egraph.nodes_of_constructor(constructor) {
                    let reachable = kept.iter().enumerate().all(|(index, symbol)| {
                        match (symbol, &node.children[index]) {
                            (GrammarSymbol::Nonterminal(name), ChildValue::Class(class)) => {
                                derivable.contains(&(name.clone(), class.clone()))
                            }
                            (GrammarSymbol::LexemeKind(_), ChildValue::Class(_)) => false,
                            (GrammarSymbol::LexemeKind(_), _) => true,
                            (GrammarSymbol::Nonterminal(_), _) => false,
                        }
                    });
                    if reachable {
                        changed |= derivable.insert((nonterminal.clone(), node.class.clone()));
                    }
                }
            }
        }
    }
    derivable
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
                    kept_positions: vec![1],
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
                    kept_positions: vec![2, 4],
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

    #[test]
    fn derivable_pairs_cover_root_and_leaves() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        let derivable = derivable_pairs(&egraph, &grammar);
        let root_class = egraph.class_of(&root).unwrap();
        let one_class = egraph.class_of(&num(1)).unwrap();
        assert!(derivable.contains(&("Expr".into(), root_class)));
        assert!(derivable.contains(&("Expr".into(), one_class)));
        assert_eq!(derivable.len(), 3);
    }

    #[test]
    fn fresh_matcher_is_feasible_iff_root_is_derivable() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        assert!(Matcher::new(root, &egraph, &grammar).nonempty());
    }

    #[test]
    fn predict_and_reads_narrow_to_the_answer() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root, &egraph, &grammar);
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Predict {
                hole: 0,
                production: 1,
                child_holes: vec![1, 2],
            },
        );
        assert!(matcher.nonempty());
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Predict {
                hole: 1,
                production: 0,
                child_holes: vec![3],
            },
        );
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Read {
                hole: 3,
                lexeme: Lexeme::number("number", 2),
            },
        );
        assert!(!matcher.nonempty());
    }

    #[test]
    fn completed_subtrees_are_reported_once() {
        let root = add(num(1), num(2));
        let egraph = with_root(&root);
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root.clone(), &egraph, &grammar);
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Predict {
                hole: 0,
                production: 0,
                child_holes: vec![1],
            },
        );
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Read {
                hole: 1,
                lexeme: Lexeme::number("number", 1),
            },
        );
        assert_eq!(matcher.take_completed(), vec![num(1)]);
        assert!(matcher.take_completed().is_empty());
    }

    #[test]
    fn refresh_recovers_feasibility_after_growth() {
        let root = add(num(1), num(2));
        let mut egraph = with_root(&root);
        let grammar = arithmetic();
        let mut matcher = Matcher::new(root, &egraph, &grammar);
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Predict {
                hole: 0,
                production: 1,
                child_holes: vec![1, 2],
            },
        );
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Predict {
                hole: 1,
                production: 0,
                child_holes: vec![3],
            },
        );
        matcher.issue(
            &egraph,
            &grammar,
            &PatternStep::Read {
                hole: 3,
                lexeme: Lexeme::number("number", 2),
            },
        );
        assert!(!matcher.nonempty());
        egraph
            .run_program("(rewrite (Add x y) (Add y x))\n(run 5)")
            .unwrap();
        matcher.refresh(&egraph, &grammar);
        assert!(matcher.nonempty());
    }
}
