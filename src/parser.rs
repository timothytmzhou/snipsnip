use crate::grammar::{Grammar, GrammarSymbol, Lexeme, ProductionId};

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

#[derive(Debug)]
pub enum ParseError {
    UnexpectedLexeme(Lexeme),
    InputComplete,
}

/// The LL(1) parser; consuming a lexeme yields the pattern steps performed.
#[derive(Debug)]
pub struct Parser {
    stack: Vec<Frame>,
    next_hole: HoleId,
    start_hole: Option<HoleId>,
}

#[derive(Debug)]
struct Frame {
    production: ProductionId,
    position: usize,
    hole_of_position: Vec<Option<HoleId>>,
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
    ) -> Result<Vec<PatternStep>, ParseError> {
        if self.start_hole.is_none() && self.stack.is_empty() {
            return Err(ParseError::InputComplete);
        }
        let mut steps = Vec::new();
        self.pop_completed(grammar);
        while let Some((nonterminal, hole)) = self.pending_nonterminal(grammar) {
            let production = grammar
                .predict(&nonterminal, &lexeme.kind)
                .ok_or_else(|| ParseError::UnexpectedLexeme(lexeme.clone()))?;
            let frame = self.expand(grammar, production, hole, &mut steps);
            self.start_hole = None;
            self.stack.push(frame);
        }
        let frame = match self.stack.last_mut() {
            Some(frame) => frame,
            None => return Err(ParseError::InputComplete),
        };
        match &grammar.production(frame.production).symbols[frame.position] {
            GrammarSymbol::LexemeKind(kind) if *kind == lexeme.kind => {
                if let Some(hole) = frame.hole_of_position[frame.position] {
                    steps.push(PatternStep::Read {
                        hole,
                        lexeme: lexeme.clone(),
                    });
                }
                frame.position += 1;
            }
            _ => return Err(ParseError::UnexpectedLexeme(lexeme.clone())),
        }
        self.pop_completed(grammar);
        Ok(steps)
    }

    /// The nonterminal awaiting expansion (start, or the top frame's current symbol), with its hole.
    fn pending_nonterminal(&self, grammar: &Grammar) -> Option<(String, Option<HoleId>)> {
        if let Some(hole) = self.start_hole {
            return Some((grammar.start().to_string(), Some(hole)));
        }
        let frame = self.stack.last()?;
        match &grammar.production(frame.production).symbols[frame.position] {
            GrammarSymbol::Nonterminal(name) => {
                Some((name.clone(), frame.hole_of_position[frame.position]))
            }
            GrammarSymbol::LexemeKind(_) => None,
        }
    }

    /// Builds the frame for a predicted production, minting holes for kept positions.
    fn expand(
        &mut self,
        grammar: &Grammar,
        production: ProductionId,
        hole: Option<HoleId>,
        steps: &mut Vec<PatternStep>,
    ) -> Frame {
        let spec = grammar.production(production);
        let mut hole_of_position = Vec::with_capacity(spec.symbols.len());
        let mut child_holes = Vec::new();
        for index in 0..spec.symbols.len() {
            if hole.is_some() && spec.kept_positions.contains(&(index + 1)) {
                let child = self.next_hole;
                self.next_hole += 1;
                child_holes.push(child);
                hole_of_position.push(Some(child));
            } else {
                hole_of_position.push(None);
            }
        }
        if let Some(hole) = hole {
            steps.push(PatternStep::Predict {
                hole,
                production,
                child_holes,
            });
        }
        Frame {
            production,
            position: 0,
            hole_of_position,
        }
    }

    /// Pops every finished frame, advancing the parent past its nonterminal.
    fn pop_completed(&mut self, grammar: &Grammar) {
        while let Some(frame) = self.stack.last() {
            if frame.position < grammar.production(frame.production).symbols.len() {
                break;
            }
            self.stack.pop();
            if let Some(parent) = self.stack.last_mut() {
                parent.position += 1;
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
        assert!(matches!(after_end, Err(ParseError::InputComplete)));
    }

    #[test]
    fn wrong_lexeme_is_rejected_without_state_change() {
        let grammar = arithmetic();
        let mut parser = Parser::new();
        parser.derivative(&grammar, &Lexeme::text("(", "(")).unwrap();
        let error = parser.derivative(&grammar, &Lexeme::text(")", ")"));
        assert!(matches!(error, Err(ParseError::UnexpectedLexeme(_))));
        assert!(parser.derivative(&grammar, &Lexeme::number("number", 1)).is_ok());
    }

    #[test]
    fn unknown_start_lexeme_is_rejected() {
        let grammar = arithmetic();
        let mut parser = Parser::new();
        let error = parser.derivative(&grammar, &Lexeme::text("+", "+"));
        assert!(matches!(error, Err(ParseError::UnexpectedLexeme(_))));
    }
}
