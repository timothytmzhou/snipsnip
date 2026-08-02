//! Streaming intersection of syntax-directed CFG prefix spaces with egglog
//! equivalence classes.

mod egglog_backend;
mod error;
mod grammar;
mod live;
pub mod paper_pwz;
mod pwz;
mod pwz_grammar;
mod realizability;

pub use error::LiveMonitorError;
pub use grammar::{
    Action, Grammar, GrammarError, LexError, NonterminalId, Production, Symbol, TerminalId, Token,
};
#[allow(deprecated)]
pub use live::DEFAULT_RELEVANT_SATURATION_ROUNDS;
pub use live::{
    DEFAULT_MANAGED_SATURATION_ROUND_LIMIT, DEFAULT_PREFIX_FOCUS_WORK_LIMIT,
    DEFAULT_PREFIX_SATURATION_ROUND_LIMIT, DEFAULT_UNREALIZABILITY_WORK_LIMIT, LiveMonitorStats,
    LivePrefixMonitor,
};
pub use pwz::{PwzError, PwzRecognizer, PwzStats};
