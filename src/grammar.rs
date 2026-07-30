use std::collections::{HashMap, HashSet};

/// A grammar symbol: a nonterminal or a lexeme kind.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GrammarSymbol {
    Nonterminal(String),
    LexemeKind(String),
}

/// One production with its AST-building action.
///
/// `kept_positions` are the 1-based, strictly increasing positions of the
/// symbols that become the children of `constructor`; other symbols are
/// dropped from the AST.
#[derive(Debug, Clone)]
pub struct Production {
    pub nonterminal: String,
    pub symbols: Vec<GrammarSymbol>,
    pub constructor: String,
    pub kept_positions: Vec<usize>,
}

/// Index of a production within a grammar.
pub type ProductionId = usize;

/// An input lexeme: a kind plus its value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexeme {
    pub kind: String,
    pub value: LexemeValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexemeValue {
    Number(i64),
    Text(String),
}

impl Lexeme {
    /// A lexeme carrying a number.
    pub fn number(kind: &str, value: i64) -> Lexeme {
        Lexeme {
            kind: kind.to_string(),
            value: LexemeValue::Number(value),
        }
    }

    /// A lexeme carrying text.
    pub fn text(kind: &str, value: &str) -> Lexeme {
        Lexeme {
            kind: kind.to_string(),
            value: LexemeValue::Text(value.to_string()),
        }
    }
}

#[derive(Debug)]
pub enum GrammarError {
    UnknownNonterminal(String),
    InvalidKeptPositions(ProductionId),
    EmptyProduction(ProductionId),
    LeftRecursive(String),
    NotLl1 { nonterminal: String, kind: String },
}

/// An LL(1) grammar with a prediction table.
#[derive(Debug, Clone)]
pub struct Grammar {
    start: String,
    productions: Vec<Production>,
    prediction: HashMap<(String, String), ProductionId>,
}

impl Grammar {
    /// Validates the productions and builds the LL(1) prediction table.
    pub fn new(start: &str, productions: Vec<Production>) -> Result<Grammar, GrammarError> {
        for (id, production) in productions.iter().enumerate() {
            if production.symbols.is_empty() {
                return Err(GrammarError::EmptyProduction(id));
            }
        }
        for (id, production) in productions.iter().enumerate() {
            let mut previous = 0;
            for &position in &production.kept_positions {
                if position <= previous || position > production.symbols.len() {
                    return Err(GrammarError::InvalidKeptPositions(id));
                }
                previous = position;
            }
        }
        let defined: HashSet<&str> = productions
            .iter()
            .map(|production| production.nonterminal.as_str())
            .collect();
        if !defined.contains(start) {
            return Err(GrammarError::UnknownNonterminal(start.to_string()));
        }
        for production in &productions {
            for symbol in &production.symbols {
                if let GrammarSymbol::Nonterminal(name) = symbol {
                    if !defined.contains(name.as_str()) {
                        return Err(GrammarError::UnknownNonterminal(name.clone()));
                    }
                }
            }
        }
        reject_left_recursion(&productions)?;
        let starting = starting_kinds(&productions);
        let mut prediction = HashMap::new();
        for (id, production) in productions.iter().enumerate() {
            let kinds: Vec<String> = match &production.symbols[0] {
                GrammarSymbol::LexemeKind(kind) => vec![kind.clone()],
                GrammarSymbol::Nonterminal(name) => {
                    starting[name.as_str()].iter().cloned().collect()
                }
            };
            for kind in kinds {
                let key = (production.nonterminal.clone(), kind.clone());
                if prediction.insert(key, id).is_some() {
                    return Err(GrammarError::NotLl1 {
                        nonterminal: production.nonterminal.clone(),
                        kind,
                    });
                }
            }
        }
        Ok(Grammar {
            start: start.to_string(),
            productions,
            prediction,
        })
    }

    pub fn start(&self) -> &str {
        &self.start
    }

    pub fn production(&self, id: ProductionId) -> &Production {
        &self.productions[id]
    }

    pub fn productions_of(&self, nonterminal: &str) -> Vec<ProductionId> {
        self.productions
            .iter()
            .enumerate()
            .filter(|(_, production)| production.nonterminal == nonterminal)
            .map(|(id, _)| id)
            .collect()
    }

    /// The nonterminals of the grammar, in first-appearance order.
    pub fn nonterminals(&self) -> Vec<String> {
        let mut seen = HashSet::new();
        let mut names = Vec::new();
        for production in &self.productions {
            if seen.insert(production.nonterminal.clone()) {
                names.push(production.nonterminal.clone());
            }
        }
        names
    }

    /// The unique production to expand `nonterminal` with on seeing `kind`.
    pub fn predict(&self, nonterminal: &str, kind: &str) -> Option<ProductionId> {
        self.prediction
            .get(&(nonterminal.to_string(), kind.to_string()))
            .copied()
    }
}

/// Fails if some nonterminal can begin a derivation of itself.
fn reject_left_recursion(productions: &[Production]) -> Result<(), GrammarError> {
    let mut edges: HashMap<&str, Vec<&str>> = HashMap::new();
    for production in productions {
        if let GrammarSymbol::Nonterminal(name) = &production.symbols[0] {
            edges
                .entry(production.nonterminal.as_str())
                .or_default()
                .push(name.as_str());
        }
    }
    let mut status: HashMap<&str, u8> = HashMap::new();
    for production in productions {
        visit_nonterminal(production.nonterminal.as_str(), &edges, &mut status)?;
    }
    Ok(())
}

/// Depth-first search that fails on reaching a nonterminal still on the path.
fn visit_nonterminal<'a>(
    node: &'a str,
    edges: &HashMap<&'a str, Vec<&'a str>>,
    status: &mut HashMap<&'a str, u8>,
) -> Result<(), GrammarError> {
    match status.get(node) {
        Some(1) => return Err(GrammarError::LeftRecursive(node.to_string())),
        Some(_) => return Ok(()),
        None => {}
    }
    status.insert(node, 1);
    if let Some(targets) = edges.get(node) {
        for &target in targets {
            visit_nonterminal(target, edges, status)?;
        }
    }
    status.insert(node, 2);
    Ok(())
}

/// Computes, per nonterminal, the lexeme kinds that can begin it, by fixpoint.
fn starting_kinds(productions: &[Production]) -> HashMap<String, HashSet<String>> {
    let mut starting: HashMap<String, HashSet<String>> = HashMap::new();
    for production in productions {
        starting.entry(production.nonterminal.clone()).or_default();
    }
    let mut changed = true;
    while changed {
        changed = false;
        for production in productions {
            let added: Vec<String> = match &production.symbols[0] {
                GrammarSymbol::LexemeKind(kind) => vec![kind.clone()],
                GrammarSymbol::Nonterminal(name) => {
                    starting[name.as_str()].iter().cloned().collect()
                }
            };
            let set = starting.get_mut(&production.nonterminal).unwrap();
            for kind in added {
                changed |= set.insert(kind);
            }
        }
    }
    starting
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn prediction_table_is_by_first_lexeme_kind() {
        let grammar = arithmetic();
        assert_eq!(grammar.predict("Expr", "number"), Some(0));
        assert_eq!(grammar.predict("Expr", "("), Some(1));
        assert_eq!(grammar.predict("Expr", "+"), None);
        assert_eq!(grammar.predict("Missing", "number"), None);
    }

    #[test]
    fn first_kinds_propagate_through_nonterminal_chains() {
        let grammar = Grammar::new(
            "Start",
            vec![
                Production {
                    nonterminal: "Start".into(),
                    symbols: vec![GrammarSymbol::Nonterminal("Middle".into())],
                    constructor: "Wrap".into(),
                    kept_positions: vec![1],
                },
                Production {
                    nonterminal: "Middle".into(),
                    symbols: vec![GrammarSymbol::LexemeKind("number".into())],
                    constructor: "Num".into(),
                    kept_positions: vec![1],
                },
            ],
        )
        .unwrap();
        assert_eq!(grammar.predict("Start", "number"), Some(0));
    }

    #[test]
    fn accessors_list_productions_and_nonterminals() {
        let grammar = arithmetic();
        assert_eq!(grammar.productions_of("Expr"), vec![0, 1]);
        assert_eq!(grammar.nonterminals(), vec!["Expr".to_string()]);
        assert_eq!(grammar.start(), "Expr");
        assert_eq!(grammar.production(1).constructor, "Add");
    }
}
