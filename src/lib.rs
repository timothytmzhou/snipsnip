//! Streaming intersection of syntax-directed CFG prefix spaces with egglog
//! equivalence classes.

mod automaton;
mod core;
mod dataflow;
mod disjoint;
mod fixed_tree;
mod forest;
mod grammar;
mod grammar_flow;
mod live;
mod monitor;
mod prefix_output;
mod product;
mod pwz;
mod realizability;

pub use automaton::{AutomatonError, RegularTreeGrammar, StateId, TreeTransition};
pub use grammar::{
    Action, Grammar, GrammarError, LexError, NonterminalId, Production, Symbol, TerminalId, Token,
};
#[allow(deprecated)]
pub use live::DEFAULT_RELEVANT_SATURATION_ROUNDS;
pub use live::{
    DEFAULT_MANAGED_SATURATION_ROUND_LIMIT, DEFAULT_PREFIX_FOCUS_WORK_LIMIT,
    DEFAULT_PREFIX_SATURATION_ROUND_LIMIT, DEFAULT_UNREALIZABILITY_WORK_LIMIT, LiveMonitorError,
    LiveMonitorStats, LivePrefixMonitor,
};
pub use monitor::{MonitorError, MonitorStats, PrefixMonitor};
pub use product::CompileError;
pub use pwz::{PwzError, PwzRecognizer, PwzStats};
