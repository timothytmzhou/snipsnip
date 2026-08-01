#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CoreSymbol {
    Nonterminal(usize),
    Terminal(usize),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct CoreProduction {
    pub(crate) lhs: usize,
    pub(crate) rhs: Vec<CoreSymbol>,
}

#[derive(Clone, Debug)]
pub(crate) struct CoreGrammar {
    pub(crate) start: usize,
    pub(crate) nonterminal_count: usize,
    pub(crate) terminal_count: usize,
    pub(crate) productions: Vec<CoreProduction>,
}
