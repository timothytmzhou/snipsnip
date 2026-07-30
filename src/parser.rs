use crate::grammar::{Grammar, GrammarSymbol, Lexeme, ProductionId};
use crate::Error;

/// Identifier of a hole in the prefix pattern.
pub type HoleId = u64;

/// One update to the prefix pattern, in the order the parser performs them.
#[derive(Debug, Clone)]
pub enum PatternStep {
    /// The hole is replaced by `constructor(child_holes...)` of the production.
    Predict {
        hole: HoleId,
        production: ProductionId,
        child_holes: Vec<HoleId>,
    },
    /// The hole is replaced by the lexeme just read.
    Read { hole: HoleId, lexeme: Lexeme },
}

/// The LL(1) parser; consuming a lexeme yields the pattern steps performed.
#[derive(Debug)]
pub struct Parser {
    stack: Vec<Item>,
    next_hole: HoleId,
    start_hole: Option<HoleId>,
}

#[derive(Debug)]
struct Item {
    production: ProductionId,
    dot: usize,
    holes: Vec<Option<HoleId>>,
}

impl Parser {
    /// A parser at the start symbol, whose pattern is the single hole 0.
    pub fn new() -> Parser {
        Parser {
            stack: Vec::new(),
            next_hole: 1,
            start_hole: Some(0),
        }
    }

    /// Consumes one lexeme; returns the pattern steps, leftmost-first.
    pub fn derivative(
        &mut self,
        grammar: &Grammar,
        lexeme: &Lexeme,
    ) -> Result<Vec<PatternStep>, Error> {
        if self.start_hole.is_none() && self.stack.is_empty() {
            return Err(Error::InputComplete);
        }
        let mut steps = Vec::new();
        self.pop_completed(grammar);
        while let Some((nonterminal, hole)) = self.pending_nonterminal(grammar) {
            let production = grammar
                .predict(&nonterminal, &lexeme.kind)
                .ok_or_else(|| Error::UnexpectedLexeme(lexeme.clone()))?;
            let item = self.predicted_item(grammar, production, hole, &mut steps);
            self.start_hole = None;
            self.stack.push(item);
        }
        let item = match self.stack.last_mut() {
            Some(item) => item,
            None => return Err(Error::InputComplete),
        };
        match &grammar.production(item.production).symbols[item.dot] {
            GrammarSymbol::LexemeKind(kind) if *kind == lexeme.kind => {
                if let Some(hole) = item.holes[item.dot] {
                    steps.push(PatternStep::Read {
                        hole,
                        lexeme: lexeme.clone(),
                    });
                }
                item.dot += 1;
            }
            _ => return Err(Error::UnexpectedLexeme(lexeme.clone())),
        }
        self.pop_completed(grammar);
        Ok(steps)
    }

    /// The nonterminal awaiting expansion (start, or the symbol at the top item's dot), with its hole.
    fn pending_nonterminal(&self, grammar: &Grammar) -> Option<(String, Option<HoleId>)> {
        if let Some(hole) = self.start_hole {
            return Some((grammar.start().to_string(), Some(hole)));
        }
        let item = self.stack.last()?;
        match &grammar.production(item.production).symbols[item.dot] {
            GrammarSymbol::Nonterminal(name) => {
                Some((name.clone(), item.holes[item.dot]))
            }
            GrammarSymbol::LexemeKind(_) => None,
        }
    }

    /// Builds the item for a predicted production, minting holes for selected positions.
    fn predicted_item(
        &mut self,
        grammar: &Grammar,
        production: ProductionId,
        hole: Option<HoleId>,
        steps: &mut Vec<PatternStep>,
    ) -> Item {
        let spec = grammar.production(production);
        let mut holes = Vec::with_capacity(spec.symbols.len());
        let mut child_holes = Vec::new();
        for index in 0..spec.symbols.len() {
            if hole.is_some() && spec.selected_positions.contains(&(index + 1)) {
                let child = self.next_hole;
                self.next_hole += 1;
                child_holes.push(child);
                holes.push(Some(child));
            } else {
                holes.push(None);
            }
        }
        if let Some(hole) = hole {
            steps.push(PatternStep::Predict {
                hole,
                production,
                child_holes,
            });
        }
        Item {
            production,
            dot: 0,
            holes,
        }
    }

    /// Pops every finished item, advancing the enclosing item past its nonterminal.
    fn pop_completed(&mut self, grammar: &Grammar) {
        while let Some(item) = self.stack.last() {
            if item.dot < grammar.production(item.production).symbols.len() {
                break;
            }
            self.stack.pop();
            if let Some(parent) = self.stack.last_mut() {
                parent.dot += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{Grammar, GrammarSymbol, Production};

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

    #[test]
    fn step_trace_for_a_full_word() {
        let grammar = arithmetic();
        let mut parser = Parser::new();

        let steps = parser.derivative(&grammar, &Lexeme::text("(", "(")).unwrap();
        assert!(matches!(
            steps.as_slice(),
            [PatternStep::Predict { hole: 0, production: 1, child_holes }] if child_holes == &vec![1, 2]
        ));

        let steps = parser.derivative(&grammar, &Lexeme::number("number", 1)).unwrap();
        assert!(matches!(
            &steps[0],
            PatternStep::Predict { hole: 1, production: 0, child_holes } if child_holes == &vec![3]
        ));
        assert!(matches!(&steps[1], PatternStep::Read { hole: 3, .. }));
        assert_eq!(steps.len(), 2);

        let steps = parser.derivative(&grammar, &Lexeme::text("+", "+")).unwrap();
        assert!(steps.is_empty());

        let steps = parser.derivative(&grammar, &Lexeme::number("number", 2)).unwrap();
        assert!(matches!(
            &steps[0],
            PatternStep::Predict { hole: 2, production: 0, child_holes } if child_holes == &vec![4]
        ));
        assert!(matches!(&steps[1], PatternStep::Read { hole: 4, .. }));

        let steps = parser.derivative(&grammar, &Lexeme::text(")", ")")).unwrap();
        assert!(steps.is_empty());

        let after_end = parser.derivative(&grammar, &Lexeme::number("number", 3));
        assert!(matches!(after_end, Err(Error::InputComplete)));
    }

    #[test]
    fn wrong_lexeme_is_rejected_without_state_change() {
        let grammar = arithmetic();
        let mut parser = Parser::new();
        parser.derivative(&grammar, &Lexeme::text("(", "(")).unwrap();
        let error = parser.derivative(&grammar, &Lexeme::text(")", ")"));
        assert!(matches!(error, Err(Error::UnexpectedLexeme(_))));
        assert!(parser.derivative(&grammar, &Lexeme::number("number", 1)).is_ok());
    }

    #[test]
    fn unknown_start_lexeme_is_rejected() {
        let grammar = arithmetic();
        let mut parser = Parser::new();
        let error = parser.derivative(&grammar, &Lexeme::text("+", "+"));
        assert!(matches!(error, Err(Error::UnexpectedLexeme(_))));
    }
}
