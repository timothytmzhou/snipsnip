use thiserror::Error;

use crate::grammar::GrammarError;

#[derive(Debug, Error)]
pub enum MonitorError {
    #[error(transparent)]
    Grammar(#[from] GrammarError),
    #[error("egglog update failed: {0}")]
    Egglog(String),
    #[error("disjointness relation `{relation}` must have signature ({sort} {sort}) -> Unit")]
    InvalidDisjointRelation { relation: String, sort: String },
    #[error("disjointness relation `Disjoint` is irreflexive, but contains an equal pair")]
    ReflexiveDisjoint,
    #[error("unknown terminal `{0}`")]
    UnknownTerminal(String),
    #[error("terminal id {0} is outside this monitor grammar's terminal range")]
    InvalidTerminalId(usize),
    #[error("lexeme `{lexeme}` is not one complete `{terminal}` token")]
    LexemeMismatch { terminal: String, lexeme: String },
    #[error("invalid distinguished binding `{binding}`: {reason}")]
    InvalidBinding { binding: String, reason: String },
    #[error("the distinguished binding has non-equality sort `{0}`")]
    NonEqualityTarget(String),
    #[error("action constructor `{0}` is not declared in the live e-graph")]
    MissingConstructor(String),
    #[error("action symbol `{0}` is an egglog function, not a datatype constructor")]
    NonConstructorAction(String),
    #[error(
        "action constructor `{constructor}` has arity {actual}, but the annotation selects {expected} child(ren)"
    )]
    ConstructorArity {
        constructor: String,
        expected: usize,
        actual: usize,
    },
    #[error(
        "terminal `{terminal}` is selected as `{sort}` data, but only String and i64 lexical children are supported"
    )]
    UnsupportedLexicalSort { terminal: String, sort: String },
    #[error(
        "semantic sort `{0}` is unsupported; live matching accepts equality sorts plus String and i64 lexical sorts"
    )]
    UnsupportedSemanticSort(String),
    #[error("terminal `{0}` is selected by an action but the grammar has no Lex specification")]
    SelectedTerminalWithoutLexer(String),
    #[error("the live monitor supports monotone egglog updates only; found `{0}`")]
    NonMonotoneUpdate(String),
    #[error("the live monitor does not execute operational egglog command `{0}`")]
    UnsupportedUpdateCommand(String),
}
