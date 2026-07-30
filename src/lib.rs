mod ast;
mod egraph;
mod grammar;
mod matcher;
mod parser;

pub use ast::Ast;
pub use grammar::{Grammar, GrammarError, GrammarSymbol, Lexeme, LexemeValue, Production};

use egraph::EGraph;
use matcher::Matcher;
use parser::Parser;

#[derive(Debug)]
pub enum Error {
    Grammar(grammar::GrammarError),
    Parse(parser::ParseError),
    EGraph(egraph::EGraphError),
}

/// The space of completions of the consumed prefix, checked against a root
/// tree held in an egglog e-graph.
pub struct PrefixSpace {
    grammar: Grammar,
    parser: Parser,
    egraph: EGraph,
    matcher: Matcher,
}

impl PrefixSpace {
    /// Loads the egglog program, inserts the root tree, and starts at the
    /// empty prefix.
    pub fn new(grammar: Grammar, egglog_program: &str, root: Ast) -> Result<PrefixSpace, Error> {
        let mut egraph = EGraph::new(egglog_program).map_err(Error::EGraph)?;
        egraph.insert_ast(&root).map_err(Error::EGraph)?;
        let matcher = Matcher::new(root, &egraph, &grammar);
        Ok(PrefixSpace {
            grammar,
            parser: Parser::new(),
            egraph,
            matcher,
        })
    }

    /// Consumes one lexeme, updating the pattern and its match state.
    pub fn derivative(&mut self, lexeme: Lexeme) -> Result<(), Error> {
        let steps = self
            .parser
            .derivative(&self.grammar, &lexeme)
            .map_err(Error::Parse)?;
        for step in &steps {
            self.matcher.issue(&self.egraph, &self.grammar, step);
        }
        for tree in self.matcher.take_completed() {
            self.egraph.insert_ast(&tree).map_err(Error::EGraph)?;
        }
        Ok(())
    }

    /// Is some completion of the prefix equal to the root tree?
    pub fn realizable(&self) -> bool {
        self.matcher.nonempty()
    }

    /// Runs the loaded rules for `iterations` and refreshes the match state.
    pub fn saturate(&mut self, iterations: u32) -> Result<(), Error> {
        self.run_program(&format!("(run {iterations})"))
    }

    /// Runs egglog commands and refreshes the match state.
    pub fn run_program(&mut self, program: &str) -> Result<(), Error> {
        self.egraph.run_program(program).map_err(Error::EGraph)?;
        self.matcher.refresh(&self.egraph, &self.grammar);
        Ok(())
    }

    /// Are the two trees provably equal in the current e-graph?
    pub fn asts_equal(&self, left: &Ast, right: &Ast) -> bool {
        match (self.egraph.class_of(left), self.egraph.class_of(right)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }
}
