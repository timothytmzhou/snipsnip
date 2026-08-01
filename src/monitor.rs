use thiserror::Error;

use crate::{
    automaton::{RegularTreeGrammar, StateId},
    grammar::{Grammar, GrammarError, RuntimeInput, TerminalId},
    product::{self, CompileError},
    pwz::{PwzError, PwzRecognizer},
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MonitorStats {
    /// Successful PwZ derivatives executed by the monitor.
    ///
    /// Calls made after the monitor reaches its absorbing empty state return
    /// the cached answer without executing or counting another derivative.
    pub derivatives: usize,
    /// Cached prefix answers produced by compilation and successful derivatives.
    ///
    /// This is `derivatives + 1`: compilation caches the answer for epsilon.
    pub cached_answers: usize,
    pub pwz_events: usize,
    pub memo_records: usize,
}

#[derive(Debug, Error)]
pub enum MonitorError {
    #[error(transparent)]
    Compile(#[from] CompileError),
    #[error(transparent)]
    Pwz(#[from] PwzError),
    #[error(transparent)]
    Grammar(#[from] GrammarError),
    #[error("unknown terminal `{0}`")]
    UnknownTerminal(String),
}

/// A streaming emptiness monitor.
///
/// All semantic/e-graph work is performed by [`compile`](Self::compile).
/// Each successful `push_*` call performs one PwZ derivative and obtains the
/// requested answer with a single check of the resulting frontier.
pub struct PrefixMonitor {
    input: RuntimeInput,
    recognizer: PwzRecognizer,
}

impl PrefixMonitor {
    pub fn compile(
        grammar: &Grammar,
        automaton: &RegularTreeGrammar,
        target: StateId,
    ) -> Result<Self, MonitorError> {
        let product = product::constrained(grammar, automaton, target)?;
        let recognizer = PwzRecognizer::compile_core(&product)?;
        Ok(Self {
            input: grammar.runtime_input(),
            recognizer,
        })
    }

    /// Pushes one grammar terminal and returns whether the intersection is empty.
    #[inline]
    pub fn push_terminal(&mut self, terminal: TerminalId) -> Result<bool, MonitorError> {
        self.push_index(terminal.index())
    }

    /// Resolves and pushes a terminal by its Yacc name.
    pub fn push_token_name(&mut self, name: &str) -> Result<bool, MonitorError> {
        let terminal = self
            .input
            .terminal(name)
            .ok_or_else(|| MonitorError::UnknownTerminal(name.to_owned()))?;
        self.push_terminal(terminal)
    }

    /// Batch-lexes text with the associated Lex specification and returns one
    /// answer per emitted (non-skip) lexeme.
    ///
    /// The exact streaming core is token based. This convenience function treats
    /// `text` as a complete Lex input, so callers that split a lexeme across chunks
    /// should buffer it or use `push_terminal`.
    pub fn push_complete_text(&mut self, text: &str) -> Result<Vec<bool>, MonitorError> {
        let mut answers = Vec::new();
        let recognizer = &mut self.recognizer;
        let mut parser_error = None;
        self.input.for_each_terminal(text, |terminal| {
            if parser_error.is_some() {
                return;
            }
            match recognizer.push_index(terminal.index()) {
                Ok(has_completion) => {
                    answers.push(!has_completion);
                }
                Err(error) => parser_error = Some(error),
            }
        })?;
        if let Some(error) = parser_error {
            return Err(error.into());
        }
        Ok(answers)
    }

    #[inline]
    fn push_index(&mut self, terminal: usize) -> Result<bool, MonitorError> {
        let has_completion = self.recognizer.push_index(terminal)?;
        Ok(!has_completion)
    }

    /// Returns the cached answer to the problem statement.
    #[inline]
    pub fn intersection_is_empty(&self) -> bool {
        !self.recognizer.has_completion()
    }

    #[inline]
    pub fn has_completion(&self) -> bool {
        self.recognizer.has_completion()
    }

    pub fn stats(&self) -> MonitorStats {
        let parser = self.recognizer.stats();
        MonitorStats {
            derivatives: parser.derivatives,
            // Compilation caches epsilon's answer, then every successful PwZ
            // derivative produces one cached Boolean.
            cached_answers: parser.derivatives.saturating_add(1),
            pwz_events: parser.events,
            memo_records: parser.memo_records,
        }
    }

    #[doc(hidden)]
    pub fn push_terminal_for_test(&mut self, terminal: usize) -> Result<bool, MonitorError> {
        self.push_index(terminal)
    }
}
