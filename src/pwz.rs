use thiserror::Error;

use crate::{
    grammar::{Grammar, GrammarError, TerminalId},
    paper_pwz::{Pwz, Token},
    pwz_grammar,
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PwzStats {
    pub derivatives: usize,
    pub events: usize,
    pub memo_records: usize,
}

#[derive(Debug, Error)]
pub enum PwzError {
    #[error(transparent)]
    Grammar(#[from] GrammarError),
    #[error("terminal id {terminal} is outside 0..{terminal_count}")]
    InvalidTerminal {
        terminal: usize,
        terminal_count: usize,
    },
}

/// Recognition-only facade over the same paper PwZ implementation used by
/// the live semantic monitor.
pub struct PwzRecognizer {
    parser: Pwz<()>,
    terminal_count: usize,
    stats: PwzStats,
}

impl PwzRecognizer {
    pub fn compile(grammar: &Grammar) -> Result<Self, PwzError> {
        Ok(Self {
            parser: Pwz::new(pwz_grammar::compile(grammar)?),
            terminal_count: grammar.terminal_count(),
            stats: PwzStats::default(),
        })
    }

    pub fn push(&mut self, terminal: TerminalId) -> Result<bool, PwzError> {
        if terminal.index() >= self.terminal_count {
            return Err(PwzError::InvalidTerminal {
                terminal: terminal.index(),
                terminal_count: self.terminal_count,
            });
        }
        if self.parser.zippers.is_empty() {
            return Ok(false);
        }
        let derivative = self.parser.derive(Token {
            terminal: u32::try_from(terminal.index()).expect("terminal count exceeds PwZ IDs"),
            payload: (),
        });
        let events = derivative.edits.len();
        let live = !derivative.zippers.is_empty();
        self.stats.derivatives = self.stats.derivatives.saturating_add(1);
        self.stats.events = self.stats.events.saturating_add(events);
        self.stats.memo_records = self.parser.memos.len();
        Ok(live)
    }

    pub fn has_completion(&self) -> bool {
        !self.parser.zippers.is_empty()
    }

    pub fn stats(&self) -> PwzStats {
        PwzStats {
            memo_records: self.parser.memos.len(),
            ..self.stats
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PwzRecognizer;
    use crate::grammar::Grammar;

    #[test]
    fn recognizes_streaming_prefixes_with_the_paper_engine() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token A B C
            %%
            start: A B { Pair(1, 2) };
            "#,
        )
        .unwrap();
        let a = grammar.terminal_by_name("A").unwrap();
        let b = grammar.terminal_by_name("B").unwrap();
        let c = grammar.terminal_by_name("C").unwrap();

        let mut accepted = PwzRecognizer::compile(&grammar).unwrap();
        assert!(accepted.has_completion());
        assert!(accepted.push(a).unwrap());
        assert!(accepted.push(b).unwrap());
        assert!(!accepted.push(c).unwrap());

        let mut rejected = PwzRecognizer::compile(&grammar).unwrap();
        assert!(!rejected.push(c).unwrap());
        assert!(!rejected.push(a).unwrap());
        assert_eq!(rejected.stats().derivatives, 1);
    }

    #[test]
    fn an_unproductive_start_has_no_completion() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %%
            start: start { $1 };
            "#,
        )
        .unwrap();
        let parser = PwzRecognizer::compile(&grammar).unwrap();
        assert!(!parser.has_completion());
    }
}
