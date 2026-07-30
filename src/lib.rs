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

/// Everything that can go wrong after grammar construction.
#[derive(Debug)]
pub enum Error {
    UnexpectedLexeme(Lexeme),
    InputComplete,
    ConstructorMismatch { constructor: String, selected: usize, arity: usize },
    EGraph(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnexpectedLexeme(lexeme) => write!(f, "unexpected lexeme of kind {}", lexeme.kind),
            Error::InputComplete => write!(f, "the word is already complete"),
            Error::ConstructorMismatch { constructor, selected, arity } => write!(
                f,
                "production selects {selected} children but constructor {constructor} takes {arity}"
            ),
            Error::EGraph(message) => write!(f, "egglog: {message}"),
        }
    }
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
        let mut egraph = EGraph::new(egglog_program)?;
        for nonterminal in grammar.nonterminals() {
            for production in grammar.productions_of(&nonterminal) {
                let spec = grammar.production(production);
                let selected = spec.selected_positions.len();
                match egraph.constructor_arity(&spec.constructor) {
                    Some(arity) if arity == selected => {}
                    Some(arity) => {
                        return Err(Error::ConstructorMismatch {
                            constructor: spec.constructor.clone(),
                            selected,
                            arity,
                        })
                    }
                    None => {
                        return Err(Error::EGraph(format!(
                            "unknown or unsupported constructor {}",
                            spec.constructor
                        )))
                    }
                }
            }
        }
        egraph.insert_ast(&root)?;
        let matcher = Matcher::new(root, &egraph, &grammar);
        Ok(PrefixSpace {
            grammar,
            parser: Parser::new(),
            egraph,
            matcher,
        })
    }

    /// Consumes one lexeme; subtrees it completes are added to the e-graph.
    pub fn derivative(&mut self, lexeme: Lexeme) -> Result<(), Error> {
        let steps = self.parser.derivative(&self.grammar, &lexeme)?;
        let completed = self.matcher.advance(&self.egraph, &self.grammar, &steps);
        for node in completed {
            self.egraph
                .insert_node(node.hole, &node.constructor, node.children.as_slice())?;
        }
        Ok(())
    }

    /// Is some completion of the prefix equal to the root tree?
    pub fn realizable(&self) -> bool {
        self.matcher.realizable()
    }

    /// Runs the loaded rules for `iterations`; the match state is refreshed
    /// only if the e-graph changed.
    pub fn saturate(&mut self, iterations: u32) -> Result<(), Error> {
        if self.egraph.saturate(iterations)? {
            self.matcher.refresh(&self.egraph, &self.grammar);
        }
        Ok(())
    }

    /// Runs egglog commands and refreshes the match state.
    pub fn run_program(&mut self, program: &str) -> Result<(), Error> {
        self.egraph.run_program(program)?;
        self.matcher.refresh(&self.egraph, &self.grammar);
        Ok(())
    }

    /// Are the two trees provably equal in the current e-graph?
    pub fn asts_equal(&self, left: &Ast, right: &Ast) -> bool {
        if left == right {
            return true;
        }
        match (self.egraph.class_of(left), self.egraph.class_of(right)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }
}
