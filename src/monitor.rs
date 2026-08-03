use std::sync::Arc;

use crate::{
    egglog_backend::{BackendDelta, EgglogBackend, MutationResult},
    error::MonitorError,
    grammar::{Grammar, RuntimeInput, TerminalId, Token},
    paper_pwz::{Change, ExpressionId, Pwz, Token as PwzToken},
    pwz_grammar,
    realizability::{RealizabilityEngine, TokenValues},
};

/// A PwZ parser, a semantic e-graph, and only the indexed links between them.
/// No parse graph or e-graph is copied into this facade.
pub struct Monitor {
    input: Arc<RuntimeInput>,
    parser: Pwz<TokenValues>,
    realizability: RealizabilityEngine,
    backend: EgglogBackend,
}

impl Monitor {
    pub fn new(
        grammar: &Grammar,
        program: &str,
        target_binding: &str,
    ) -> Result<Self, MonitorError> {
        let input = Arc::new(grammar.runtime_input());
        let init = EgglogBackend::initialize(grammar, input.clone(), program, target_binding)?;
        let semantic_schema = pwz_grammar::semantics(
            grammar,
            |name| init.schema.constructor_id(name),
            init.schema.constructors.clone(),
        );
        let parser = Pwz::new(pwz_grammar::compile(grammar)?);
        let realizability = RealizabilityEngine::new(semantic_schema, &parser, &init.backend);
        let mut monitor = Self {
            input,
            parser,
            realizability,
            backend: init.backend,
        };
        if monitor.realizability().is_none() {
            monitor.synchronize(&[])?;
        }
        Ok(monitor)
    }

    pub fn push_token_name(
        &mut self,
        terminal_name: &str,
        lexeme: &str,
    ) -> Result<Option<bool>, MonitorError> {
        let terminal = self
            .input
            .terminal(terminal_name)
            .ok_or_else(|| MonitorError::UnknownTerminal(terminal_name.to_owned()))?;
        if self.input.has_lexer() && !self.input.lexeme_matches(terminal, lexeme) {
            return Err(MonitorError::LexemeMismatch {
                terminal: terminal_name.to_owned(),
                lexeme: lexeme.to_owned(),
            });
        }
        self.push_lexeme(terminal, lexeme)
    }

    pub fn push_token(&mut self, token: &Token) -> Result<Option<bool>, MonitorError> {
        self.push_lexeme(token.kind, &token.lexeme)
    }

    pub fn push_complete_text(&mut self, text: &str) -> Result<Vec<Option<bool>>, MonitorError> {
        let mut answers = Vec::new();
        for token in self.input.lex(text)? {
            answers.push(self.push_token(&token)?);
        }
        Ok(answers)
    }

    pub fn push_lexeme(
        &mut self,
        terminal: TerminalId,
        lexeme: &str,
    ) -> Result<Option<bool>, MonitorError> {
        if terminal.index() >= self.backend.terminal_count() {
            return Err(MonitorError::InvalidTerminalId(terminal.index()));
        }
        if self.parser.zippers().is_empty() {
            return Ok(Some(false));
        }
        let mut payload = TokenValues::new();
        self.backend.exact_tokens(terminal, lexeme, &mut payload)?;
        let changes = self.parser.derive(PwzToken {
            terminal: u32::try_from(terminal.index())
                .map_err(|_| MonitorError::InvalidTerminalId(terminal.index()))?,
            payload,
        });
        self.realizability
            .update_pwz(&self.parser, &changes, &self.backend);
        if self.parser.zippers().is_empty() {
            return Ok(Some(false));
        }
        if self.has_witness() {
            return Ok(Some(true));
        }
        let fixed = changes
            .iter()
            .filter_map(|change| match change {
                Change::NewExpression(expression) => Some(*expression),
                _ => None,
            })
            .collect::<Vec<_>>();
        self.synchronize(&fixed)?;
        Ok(self.realizability())
    }

    /// Adds monotone Egglog commands and updates the intersection. Rewrites
    /// use the same focused scheduling as rewrites in the initial program.
    pub fn run_egglog(&mut self, update: &str) -> Result<Option<bool>, MonitorError> {
        let mutation = self.backend.apply_monotone_update(update)?;
        let partial = match mutation {
            MutationResult::Applied => None,
            MutationResult::PartiallyApplied(error) => Some(error),
        };
        let result = self.finish_egraph_update();
        match (partial, result) {
            (None, result) => result,
            (Some(error), Ok(_)) => Err(error),
            (Some(error), Err(sync)) => Err(MonitorError::Egglog(format!(
                "{error}; additionally failed to synchronize the partial update: {sync}"
            ))),
        }
    }

    pub fn realizability(&self) -> Option<bool> {
        if self.parser.zippers().is_empty() {
            Some(false)
        } else if self.has_witness() {
            Some(true)
        } else if self
            .realizability
            .is_unrealizable(&self.parser, &self.backend)
        {
            Some(false)
        } else {
            None
        }
    }

    fn finish_egraph_update(&mut self) -> Result<Option<bool>, MonitorError> {
        let delta = self.backend.flush_changes()?;
        self.apply_delta(delta);
        if let Some(answer) = self.realizability() {
            return Ok(Some(answer));
        }
        self.synchronize(&[])?;
        Ok(self.realizability())
    }

    fn synchronize(&mut self, new_fixed: &[ExpressionId]) -> Result<(), MonitorError> {
        self.backend.begin_focus();
        self.materialize(new_fixed)?;
        let delta = self.backend.flush_changes()?;
        self.apply_delta(delta);
        if self.realizability().is_some() {
            return Ok(());
        }

        loop {
            let delta = self.backend.saturate_local()?;
            let updated = delta.updated;
            let changed_intersection = !delta.changes.is_empty();
            self.apply_delta(delta);
            if self.realizability().is_some() {
                return Ok(());
            }

            if changed_intersection {
                let focus_changed = self.materialize(&[])?;
                let delta = self.backend.flush_changes()?;
                self.apply_delta(delta);
                if self.realizability().is_some() {
                    return Ok(());
                }
                if focus_changed {
                    continue;
                }
            }
            if !updated {
                return Ok(());
            }
        }
    }

    fn apply_delta(&mut self, delta: BackendDelta) {
        self.realizability
            .update_egraph(&self.parser, &delta.changes, &self.backend);
    }

    fn materialize(&mut self, expressions: &[ExpressionId]) -> Result<bool, MonitorError> {
        let fixed =
            self.realizability
                .materialize_fixed(&self.parser, expressions, &mut self.backend)?;
        let focus = self
            .realizability
            .materialize_focus(&self.parser, &mut self.backend)?;
        Ok(fixed || focus)
    }

    fn has_witness(&self) -> bool {
        self.realizability
            .is_realizable(&self.parser, &self.backend)
    }
}

#[cfg(test)]
mod tests {
    use super::Monitor;
    use crate::grammar::Grammar;

    #[test]
    fn checks_each_prefix_and_applies_late_equality_without_parser_replay() {
        let grammar = Grammar::from_yacc_lex(
            r#"
            %start start
            %token ID
            %%
            start: ID { Var(1) };
            "#,
            "%%\n[a-z]+ 'ID'\n",
        )
        .unwrap();
        let mut monitor = Monitor::new(
            &grammar,
            r#"
            (datatype Ast (Var String))
            (let $root (Var "x"))
            "#,
            "$root",
        )
        .unwrap();

        assert_eq!(monitor.realizability(), Some(true));
        monitor.push_token_name("ID", "y").unwrap();
        assert_eq!(monitor.realizability(), None);
        monitor.run_egglog("(union $root (Var \"y\"))").unwrap();
        assert_eq!(monitor.realizability(), Some(true));
    }

    #[test]
    fn ignored_future_syntax_uses_the_value_independent_relation() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token TAIL
            %%
            start: TAIL { Good() };
            "#,
        )
        .unwrap();
        let monitor = Monitor::new(
            &grammar,
            "(datatype Ast (Good)) (let $root (Good))",
            "$root",
        )
        .unwrap();
        assert_eq!(monitor.realizability(), Some(true));
    }

    #[test]
    fn focus_materialization_crosses_ignored_pending_syntax() {
        let grammar = Grammar::from_yacc(
            r#"
            %start start
            %token BAD TAIL
            %%
            start: atom TAIL { Wrap(1) };
            atom: BAD { Bad() };
            "#,
        )
        .unwrap();
        let mut monitor = Monitor::new(
            &grammar,
            r#"
            (datatype Ast (Good) (Bad) (Wrap Ast))
            (let $root (Good))
            (rewrite (Wrap (Bad)) (Good))
            "#,
            "$root",
        )
        .unwrap();
        monitor.push_token_name("BAD", "bad").unwrap();
        assert_eq!(monitor.realizability(), Some(true));
    }
}
