use std::{
    collections::{HashMap, VecDeque},
    sync::{Arc, OnceLock},
};

use cfgrammar::{
    Symbol as YaccSymbol,
    yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
};
use lrlex::{DefaultLexerTypes, LRNonStreamingLexerDef, LexerDef};
use regex::{Regex, RegexBuilder};
use regex_automata::{
    Anchored, Input, MatchKind,
    dfa::{Automaton, StartKind, dense},
    util::{primitives::StateID, syntax},
};
use regex_syntax::ParserBuilder as RegexSyntaxParserBuilder;
use regex_syntax::hir::Look;
use rustc_hash::FxHashSet as HashSet;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NonterminalId(pub(crate) usize);

impl NonterminalId {
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TerminalId(pub(crate) usize);

impl TerminalId {
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Symbol {
    Nonterminal(NonterminalId),
    Terminal(TerminalId),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Action {
    Construct {
        constructor: String,
        /// One-based positions in the production right-hand side.
        arguments: Vec<usize>,
    },
    /// Return one RHS semantic value without constructing a wrapper.
    Project {
        /// One-based position in the production right-hand side.
        position: usize,
    },
}

impl Action {
    pub fn constructor(&self) -> Option<&str> {
        match self {
            Self::Construct { constructor, .. } => Some(constructor),
            Self::Project { .. } => None,
        }
    }

    pub fn arguments(&self) -> &[usize] {
        match self {
            Self::Construct { arguments, .. } => arguments,
            Self::Project { position } => std::slice::from_ref(position),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Production {
    pub lhs: NonterminalId,
    pub rhs: Vec<Symbol>,
    pub action: Action,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TerminalId,
    pub lexeme: String,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Error)]
pub enum GrammarError {
    #[error("invalid Yacc grammar: {0}")]
    Yacc(String),
    #[error("invalid Lex specification: {0}")]
    Lex(String),
    #[error("production {production} has no simple linear action")]
    MissingAction { production: usize },
    #[error("invalid action `{action}` on production {production}: {reason}")]
    InvalidAction {
        production: usize,
        action: String,
        reason: String,
    },
    #[error("Lex does not define grammar token(s): {0}")]
    MissingLexRules(String),
    #[error("Lex defines named rule(s) absent from the grammar: {0}")]
    UnusedLexRules(String),
    #[error("lexer start conditions and transitions are not supported")]
    LexerStatesUnsupported,
    #[error("lexer rule `{0}` accepts the empty string")]
    NullableLexRule(String),
    #[error("unsupported Yacc feature: {0}")]
    UnsupportedYaccFeature(String),
    #[error("unsupported Lex feature: {0}")]
    UnsupportedLexFeature(String),
    #[error("complete-lexeme productivity is unavailable: {0}")]
    LexicalProductivity(String),
    #[error("this grammar has no Lex specification")]
    NoLexer,
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum LexError {
    #[error("no lexer rule matches byte {offset}")]
    NoMatch { offset: usize },
    #[error("lexer rule `{rule}` matched zero bytes at byte {offset}")]
    ZeroLengthRule { offset: usize, rule: String },
    #[error("lexer automaton failed at byte {offset}: {reason}")]
    Engine { offset: usize, reason: String },
}

#[derive(Clone)]
struct LexRule {
    source: String,
    terminal: Option<TerminalId>,
    dfa: dense::DFA<Vec<u32>>,
    unicode_fallback: Option<Regex>,
}

#[derive(Clone)]
struct LexMachine {
    rules: Vec<LexRule>,
    complete_lexeme_terminals: OnceLock<Result<Box<[bool]>, String>>,
}

#[derive(Clone)]
pub(crate) struct RuntimeInput {
    terminal_by_name: HashMap<String, TerminalId>,
    lexer: Option<Arc<LexMachine>>,
}

impl RuntimeInput {
    pub(crate) fn terminal(&self, name: &str) -> Option<TerminalId> {
        self.terminal_by_name.get(name).copied()
    }

    pub(crate) fn lex(&self, input: &str) -> Result<Vec<Token>, GrammarError> {
        let machine = self.lexer.as_ref().ok_or(GrammarError::NoLexer)?;
        lex_with_machine(machine, input).map_err(|error| GrammarError::Lex(error.to_string()))
    }

    pub(crate) fn has_lexer(&self) -> bool {
        self.lexer.is_some()
    }

    /// Returns whether `lexeme`, considered as one complete lexer input,
    /// emits exactly `terminal` and consumes no ignored prefix or suffix.
    pub(crate) fn lexeme_matches(&self, terminal: TerminalId, lexeme: &str) -> bool {
        let Some(machine) = &self.lexer else {
            return false;
        };
        let mut matched = false;
        let result = scan_with_machine(machine, lexeme, |kind, _, start, end| {
            matched = !matched && kind == terminal && start == 0 && end == lexeme.len();
        });
        result.is_ok() && matched
    }

    /// Returns whether some decimal spelling parsed by `i64::from_str`
    /// denotes `value` and is emitted as exactly `terminal`.
    ///
    /// Integer values can have infinitely many spellings because leading
    /// zeroes are accepted.  We decide existence without imposing an
    /// arbitrary spelling-length bound: after the optional sign, repeatedly
    /// reading `0` eventually cycles in the finite product of the lexer-rule
    /// DFA states.  Equal product states have equal behaviour on the fixed
    /// canonical digit suffix.
    pub(crate) fn i64_lexeme_matches(&self, terminal: TerminalId, value: i64) -> bool {
        let Some(machine) = &self.lexer else {
            return false;
        };
        let digits = value.unsigned_abs().to_string();
        let signs: &[u8] = if value < 0 {
            b"-"
        } else if value == 0 {
            // A zero may be unsigned, explicitly positive, or negative.
            b"\0+-"
        } else {
            b"\0+"
        };
        signs.iter().any(|sign| {
            let sign = (*sign != 0).then_some(*sign);
            machine.integer_spelling_matches(terminal, sign, digits.as_bytes())
        })
    }
}

impl LexMachine {
    fn complete_lexeme_terminals(&self, terminal_count: usize) -> Result<&[bool], GrammarError> {
        match self
            .complete_lexeme_terminals
            .get_or_init(|| self.compute_complete_lexeme_terminals(terminal_count))
        {
            Ok(terminals) => Ok(terminals),
            Err(reason) => Err(GrammarError::LexicalProductivity(reason.clone())),
        }
    }

    fn compute_complete_lexeme_terminals(
        &self,
        terminal_count: usize,
    ) -> Result<Box<[bool]>, String> {
        if self
            .rules
            .iter()
            .any(|rule| rule.unicode_fallback.is_some())
        {
            return Err("Unicode word-boundary fallback cannot yet be analyzed exactly".to_owned());
        }
        if self.rules.is_empty() {
            return Ok(vec![false; terminal_count].into_boxed_slice());
        }

        let mut inhabited = vec![false; terminal_count];
        let mut missing = terminal_count;
        let mut seen = HashSet::default();
        let mut pending = VecDeque::new();

        // Keep the existing per-rule leftmost-first DFAs. Recompiling all
        // patterns with `MatchKind::All` would be wrong for ordered choices
        // such as `a|ab`: the actual rule commits to `a`, which lets a later
        // `ab` rule win by maximal munch.
        //
        // Anchored DFA start states may inspect the first byte to resolve
        // look-around. Seed the product graph once for each possible first
        // byte; nullable lexer rules have already been rejected.
        for byte in u8::MIN..=u8::MAX {
            let first = [byte];
            let input = Input::new(&first).anchored(Anchored::Yes);
            let mut states = Vec::with_capacity(self.rules.len());
            let mut any_live = false;
            for rule in &self.rules {
                let start = rule
                    .dfa
                    .start_state_forward(&input)
                    .map_err(|error| error.to_string())?;
                let state = rule.dfa.next_state(start, byte);
                if rule.dfa.is_quit_state(state) {
                    return Err(format!("lexer DFA quit on byte {byte}"));
                }
                any_live |= !rule.dfa.is_dead_state(state);
                states.push(state);
            }
            if any_live && seen.insert(states.clone()) {
                pending.push_back(states);
            }
        }

        while let Some(states) = pending.pop_front() {
            let mut winning_rule = None;
            for (index, (rule, state)) in self.rules.iter().zip(&states).enumerate() {
                let eoi = rule.dfa.next_eoi_state(*state);
                if rule.dfa.is_quit_state(eoi) {
                    return Err("lexer DFA quit at end of input".to_owned());
                }
                if rule.dfa.is_match_state(eoi) {
                    winning_rule = Some(index);
                    break;
                }
            }
            if let Some(winning_rule) = winning_rule
                && let Some(terminal) = self.rules[winning_rule].terminal
                && !inhabited[terminal.index()]
            {
                inhabited[terminal.index()] = true;
                missing -= 1;
                // Normal lexers finish here after finding one short concrete
                // witness per token. Exhausting the product is needed only to
                // prove a genuinely shadowed rule.
                if missing == 0 {
                    return Ok(inhabited.into_boxed_slice());
                }
            }

            if seen.len() > 100_000 {
                return Err(
                    "lexer-rule overlap exceeded the exact productivity work limit".to_owned(),
                );
            }

            for byte in u8::MIN..=u8::MAX {
                let mut next_states = Vec::with_capacity(self.rules.len());
                let mut any_live = false;
                for (rule, state) in self.rules.iter().zip(&states) {
                    let next = rule.dfa.next_state(*state, byte);
                    if rule.dfa.is_quit_state(next) {
                        return Err(format!("lexer DFA quit on byte {byte}"));
                    }
                    any_live |= !rule.dfa.is_dead_state(next);
                    next_states.push(next);
                }
                if any_live && seen.insert(next_states.clone()) {
                    pending.push_back(next_states);
                }
            }
        }
        Ok(inhabited.into_boxed_slice())
    }

    fn integer_spelling_matches(
        &self,
        terminal: TerminalId,
        sign: Option<u8>,
        digits: &[u8],
    ) -> bool {
        // Start-state look-around can inspect whether the first byte is a word
        // byte.  Use a representative with the same optional sign and a digit
        // first byte as every spelling considered below.
        let mut representative = Vec::with_capacity(1 + digits.len());
        if let Some(sign) = sign {
            representative.push(sign);
        }
        representative.push(b'0');
        representative.extend_from_slice(digits);
        let input = Input::new(&representative).anchored(Anchored::Yes);
        let mut states = Vec::with_capacity(self.rules.len());
        for rule in &self.rules {
            let Ok(mut state) = rule.dfa.start_state_forward(&input) else {
                return false;
            };
            if let Some(sign) = sign {
                state = rule.dfa.next_state(state, sign);
                if rule.dfa.is_quit_state(state) {
                    return false;
                }
            }
            states.push(state);
        }

        let accepts_terminal = |states: &[StateID]| {
            self.rules
                .iter()
                .zip(states)
                .find_map(|(rule, state)| {
                    let mut state = *state;
                    for &byte in digits {
                        state = rule.dfa.next_state(state, byte);
                        if rule.dfa.is_dead_state(state) || rule.dfa.is_quit_state(state) {
                            return None;
                        }
                    }
                    let state = rule.dfa.next_eoi_state(state);
                    rule.dfa.is_match_state(state).then_some(rule.terminal)
                })
                .flatten()
                == Some(terminal)
        };
        let advance_zero = |states: &mut [StateID]| {
            for (rule, state) in self.rules.iter().zip(states) {
                *state = rule.dfa.next_state(*state, b'0');
                if rule.dfa.is_quit_state(*state) {
                    return false;
                }
            }
            true
        };

        // Brent's detector visits every state in the deterministic zero-prefix
        // sequence while retaining only two state vectors.
        if accepts_terminal(&states) {
            return true;
        }
        let mut anchor = states.clone();
        if !advance_zero(&mut states) {
            return false;
        }
        let mut power = 1usize;
        let mut span = 1usize;
        loop {
            if accepts_terminal(&states) {
                return true;
            }
            if states == anchor {
                return false;
            }
            if span == power {
                anchor.clone_from(&states);
                power = power.saturating_mul(2);
                span = 0;
            }
            if !advance_zero(&mut states) {
                return false;
            }
            span = span.saturating_add(1);
        }
    }
}

#[derive(Clone)]
pub struct Grammar {
    start: NonterminalId,
    nonterminal_names: Vec<String>,
    terminal_names: Vec<String>,
    terminal_by_name: HashMap<String, TerminalId>,
    productions: Vec<Production>,
    lexer: Option<Arc<LexMachine>>,
}

impl std::fmt::Debug for Grammar {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Grammar")
            .field("start", &self.start)
            .field("nonterminal_names", &self.nonterminal_names)
            .field("terminal_names", &self.terminal_names)
            .field("productions", &self.productions)
            .field("has_lexer", &self.lexer.is_some())
            .finish()
    }
}

impl Grammar {
    /// Parses an annotated, original-style Yacc grammar.
    ///
    /// Every user production must carry an action such as `{ Add(1, 3) }`.
    pub fn from_yacc(yacc: &str) -> Result<Self, GrammarError> {
        Self::build(yacc, None)
    }

    /// Parses an annotated Yacc grammar and a Lex lexer specification.
    pub fn from_yacc_lex(yacc: &str, lex: &str) -> Result<Self, GrammarError> {
        Self::build(yacc, Some(lex))
    }

    fn build(yacc: &str, lex: Option<&str>) -> Result<Self, GrammarError> {
        let parsed = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            yacc,
        )
        .map_err(|errors| {
            GrammarError::Yacc(
                errors
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; "),
            )
        })?;
        if parsed.programs().is_some()
            || parsed.parse_param().is_some()
            || parsed.parse_generics().is_some()
        {
            return Err(GrammarError::UnsupportedYaccFeature(
                "embedded programs, parse parameters, and parse generics".to_owned(),
            ));
        }
        if parsed
            .iter_pidxs()
            .any(|production| parsed.prod_precedence(production).is_some())
        {
            return Err(GrammarError::UnsupportedYaccFeature(
                "precedence and associativity declarations (PwZ consumes the raw CFG)".to_owned(),
            ));
        }

        let synthetic_start = parsed.start_rule_idx();
        let start_production = parsed.prod(parsed.start_prod());
        let user_start_rule = match start_production {
            [YaccSymbol::Rule(rule)] => *rule,
            _ => {
                return Err(GrammarError::Yacc(
                    "cfgrammar produced an invalid synthetic start rule".to_owned(),
                ));
            }
        };

        let mut rule_map = HashMap::new();
        let mut nonterminal_names = Vec::new();
        for rule in parsed.iter_rules().filter(|rule| *rule != synthetic_start) {
            let id = NonterminalId(nonterminal_names.len());
            rule_map.insert(rule, id);
            nonterminal_names.push(parsed.rule_name_str(rule).to_owned());
        }
        let start = rule_map[&user_start_rule];

        let mut token_map = HashMap::new();
        let mut terminal_names = Vec::new();
        let mut terminal_by_name = HashMap::new();
        for token in parsed
            .iter_tidxs()
            .filter(|token| *token != parsed.eof_token_idx())
        {
            let Some(name) = parsed.token_name(token) else {
                continue;
            };
            let id = TerminalId(terminal_names.len());
            token_map.insert(token, id);
            terminal_names.push(name.to_owned());
            terminal_by_name.insert(name.to_owned(), id);
        }

        let mut productions = Vec::new();
        for production_index in parsed
            .iter_pidxs()
            .filter(|index| *index != parsed.start_prod())
        {
            let raw_index = usize::from(production_index);
            let lhs = rule_map[&parsed.prod_to_rule(production_index)];
            let rhs = parsed
                .prod(production_index)
                .iter()
                .map(|symbol| match symbol {
                    YaccSymbol::Rule(rule) => Symbol::Nonterminal(rule_map[rule]),
                    YaccSymbol::Token(token) => Symbol::Terminal(token_map[token]),
                })
                .collect::<Vec<_>>();
            let action_source =
                parsed
                    .action(production_index)
                    .as_deref()
                    .ok_or(GrammarError::MissingAction {
                        production: raw_index,
                    })?;
            let action =
                parse_action(action_source).map_err(|reason| GrammarError::InvalidAction {
                    production: raw_index,
                    action: action_source.to_owned(),
                    reason,
                })?;
            validate_action(&action, &rhs).map_err(|reason| GrammarError::InvalidAction {
                production: raw_index,
                action: action_source.to_owned(),
                reason,
            })?;
            productions.push(Production { lhs, rhs, action });
        }

        let lexer = lex
            .map(|source| build_lexer(source, &parsed, &terminal_by_name))
            .transpose()?;

        Ok(Self {
            start,
            nonterminal_names,
            terminal_names,
            terminal_by_name,
            productions,
            lexer,
        })
    }

    pub fn start(&self) -> NonterminalId {
        self.start
    }

    pub fn nonterminal_name(&self, id: NonterminalId) -> &str {
        &self.nonterminal_names[id.0]
    }

    pub fn terminal_name(&self, id: TerminalId) -> &str {
        &self.terminal_names[id.0]
    }

    pub fn terminal_by_name(&self, name: &str) -> Option<TerminalId> {
        self.terminal_by_name.get(name).copied()
    }

    pub fn productions(&self) -> &[Production] {
        &self.productions
    }

    pub fn nonterminal_count(&self) -> usize {
        self.nonterminal_names.len()
    }

    pub fn terminal_count(&self) -> usize {
        self.terminal_names.len()
    }

    /// Returns exactly which terminals have at least one complete lexeme.
    ///
    /// Grammars without a Lex specification consume abstract terminals, so
    /// every declared terminal is inhabited. Lexer-backed grammars account
    /// for maximal munch, rule priority, and ignored rules.
    pub(crate) fn complete_lexeme_terminals(&self) -> Result<Box<[bool]>, GrammarError> {
        let Some(machine) = &self.lexer else {
            return Ok(vec![true; self.terminal_count()].into_boxed_slice());
        };
        Ok(machine
            .complete_lexeme_terminals(self.terminal_count())?
            .to_vec()
            .into_boxed_slice())
    }

    pub fn lex(&self, input: &str) -> Result<Vec<Token>, GrammarError> {
        let machine = self.lexer.as_ref().ok_or(GrammarError::NoLexer)?;
        lex_with_machine(machine, input).map_err(|error| GrammarError::Lex(error.to_string()))
    }

    pub(crate) fn runtime_input(&self) -> RuntimeInput {
        RuntimeInput {
            terminal_by_name: self.terminal_by_name.clone(),
            lexer: self.lexer.clone(),
        }
    }
}

fn parse_action(source: &str) -> Result<Action, String> {
    let source = source.trim();
    if let Some(position) = source.strip_prefix('$') {
        let position = position
            .parse::<usize>()
            .map_err(|_| "expected `$<natural-number position>`".to_owned())?;
        return Ok(Action::Project { position });
    }
    let open = source
        .find('(')
        .ok_or_else(|| "expected `Constructor(...)`".to_owned())?;
    if !source.ends_with(')') {
        return Err("expected a closing `)`".to_owned());
    }
    let constructor = source[..open].trim();
    if constructor.is_empty()
        || constructor
            .chars()
            .any(|character| character.is_whitespace() || "(),{}".contains(character))
    {
        return Err("constructor must be a single egglog symbol".to_owned());
    }
    let arguments_source = &source[open + 1..source.len() - 1];
    let arguments = if arguments_source.trim().is_empty() {
        Vec::new()
    } else {
        arguments_source
            .split(',')
            .map(|argument| {
                argument
                    .trim()
                    .parse::<usize>()
                    .map_err(|_| format!("`{argument}` is not a natural-number position"))
            })
            .collect::<Result<Vec<_>, _>>()?
    };
    if arguments.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err("argument positions must be strictly increasing".to_owned());
    }
    Ok(Action::Construct {
        constructor: constructor.to_owned(),
        arguments,
    })
}

fn validate_action(action: &Action, rhs: &[Symbol]) -> Result<(), String> {
    for &position in action.arguments() {
        if position == 0 || position > rhs.len() {
            return Err(format!(
                "argument position {position} is outside the 1..={} right-hand side",
                rhs.len()
            ));
        }
    }
    Ok(())
}

fn build_lexer(
    source: &str,
    parsed: &YaccGrammar<u32>,
    terminal_by_name: &HashMap<String, TerminalId>,
) -> Result<Arc<LexMachine>, GrammarError> {
    let normalized = dedent(source);
    if normalized.trim_start().starts_with("%grmtools") {
        return Err(GrammarError::UnsupportedLexFeature(
            "custom %grmtools Lex flags".to_owned(),
        ));
    }
    let mut lexer = LRNonStreamingLexerDef::<DefaultLexerTypes<u32>>::from_str(&normalized)
        .map_err(|errors| {
            GrammarError::Lex(
                errors
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; "),
            )
        })?;

    let yacc_tokens = parsed
        .tokens_map()
        .into_iter()
        .map(|(name, index)| (name, u32::try_from(usize::from(index)).unwrap()))
        .collect::<HashMap<_, _>>();
    let (missing_from_lexer, unused_lexer_rules) = lexer.set_rule_ids(&yacc_tokens);
    if let Some(missing) = missing_from_lexer
        && !missing.is_empty()
    {
        let mut names = missing.into_iter().collect::<Vec<_>>();
        names.sort_unstable();
        return Err(GrammarError::MissingLexRules(names.join(", ")));
    }
    if let Some(unused) = unused_lexer_rules
        && !unused.is_empty()
    {
        let mut names = unused.into_iter().collect::<Vec<_>>();
        names.sort_unstable();
        return Err(GrammarError::UnusedLexRules(names.join(", ")));
    }

    let mut rules = Vec::new();
    for rule in lexer.iter_rules() {
        if (!rule.start_states().is_empty() && rule.start_states() != [0])
            || rule.target_state().is_some()
        {
            return Err(GrammarError::LexerStatesUnsupported);
        }
        let hir = RegexSyntaxParserBuilder::new()
            .octal(true)
            .build()
            .parse(rule.re_str())
            .map_err(|error| GrammarError::Lex(format!("{}: {error}", rule.re_str())))?;
        if hir.properties().minimum_len() == Some(0) {
            return Err(GrammarError::NullableLexRule(rule.re_str().to_owned()));
        }
        let looks = hir.properties().look_set();
        let has_unicode_word_boundary = [
            Look::WordUnicode,
            Look::WordUnicodeNegate,
            Look::WordStartUnicode,
            Look::WordEndUnicode,
            Look::WordStartHalfUnicode,
            Look::WordEndHalfUnicode,
        ]
        .into_iter()
        .any(|look| looks.contains(look));
        // `lrlex` may leave an internal numeric ID on an ignored rule. Those
        // IDs share a number space with Yacc token IDs but do not denote a
        // token. A rule emits only when it has an explicit token name.
        let terminal = rule
            .name()
            .and_then(|name| terminal_by_name.get(name).copied());
        let dfa = dense::Builder::new()
            .configure(
                dense::Config::new()
                    .start_kind(StartKind::Anchored)
                    .match_kind(MatchKind::LeftmostFirst)
                    .unicode_word_boundary(has_unicode_word_boundary),
            )
            .syntax(
                syntax::Config::new()
                    .dot_matches_new_line(true)
                    .multi_line(true)
                    .octal(true),
            )
            .build(rule.re_str())
            .map_err(|error| GrammarError::Lex(error.to_string()))?;
        let unicode_fallback = has_unicode_word_boundary
            .then(|| {
                RegexBuilder::new(&format!(r"\A(?:{})", rule.re_str()))
                    .dot_matches_new_line(true)
                    .multi_line(true)
                    .octal(true)
                    .build()
                    .map_err(|error| GrammarError::Lex(error.to_string()))
            })
            .transpose()?;
        rules.push(LexRule {
            source: rule.re_str().to_owned(),
            terminal,
            dfa,
            unicode_fallback,
        });
    }
    Ok(Arc::new(LexMachine {
        rules,
        complete_lexeme_terminals: OnceLock::new(),
    }))
}

fn dedent(source: &str) -> String {
    let indentation = source
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            line.as_bytes()
                .iter()
                .take_while(|byte| matches!(byte, b' ' | b'\t'))
                .count()
        })
        .min()
        .unwrap_or(0);
    if indentation == 0 {
        return source.to_owned();
    }
    source
        .lines()
        .map(|line| {
            if line.trim().is_empty() {
                ""
            } else {
                &line[indentation..]
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn lex_with_machine(machine: &LexMachine, input: &str) -> Result<Vec<Token>, LexError> {
    let mut output = Vec::new();
    scan_with_machine(machine, input, |kind, lexeme, start, end| {
        output.push(Token {
            kind,
            lexeme: lexeme.to_owned(),
            start,
            end,
        });
    })?;
    Ok(output)
}

fn scan_with_machine(
    machine: &LexMachine,
    input: &str,
    mut emit: impl FnMut(TerminalId, &str, usize, usize),
) -> Result<(), LexError> {
    let mut memo = (0..machine.rules.len())
        .map(|_| HashMap::<(usize, StateID), Option<usize>>::new())
        .collect::<Vec<_>>();
    let input_is_ascii = input.is_ascii();
    let mut offset = 0;
    while offset < input.len() {
        let mut best = None;
        for (rule_index, rule) in machine.rules.iter().enumerate() {
            let Some(end) = rule_match(rule, input, input_is_ascii, offset, &mut memo[rule_index])?
            else {
                continue;
            };
            best = better_match(
                best,
                Some(LexMatch {
                    end,
                    rule: rule_index,
                }),
            );
        }
        let Some(best) = best else {
            return Err(LexError::NoMatch { offset });
        };
        let length = best.end - offset;
        let rule = &machine.rules[best.rule];
        if length == 0 {
            return Err(LexError::ZeroLengthRule {
                offset,
                rule: rule.source.clone(),
            });
        }
        if let Some(kind) = rule.terminal {
            emit(kind, &input[offset..best.end], offset, best.end);
        }
        offset += length;
    }
    Ok(())
}

fn rule_match(
    rule: &LexRule,
    input: &str,
    input_is_ascii: bool,
    offset: usize,
    memo: &mut HashMap<(usize, StateID), Option<usize>>,
) -> Result<Option<usize>, LexError> {
    if !input_is_ascii && let Some(regex) = &rule.unicode_fallback {
        let suffix = &input[offset..];
        return Ok(regex.find(suffix).map(|matched| {
            debug_assert_eq!(matched.start(), 0);
            offset + matched.end()
        }));
    }
    dfa_rule_match(rule, input.as_bytes(), offset, memo)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LexMatch {
    end: usize,
    rule: usize,
}

fn dfa_rule_match(
    rule: &LexRule,
    input: &[u8],
    offset: usize,
    memo: &mut HashMap<(usize, StateID), Option<usize>>,
) -> Result<Option<usize>, LexError> {
    // lrlex applies each anchored regex to `&input[offset..]`, so BOI and
    // word-boundary context restart at every token boundary.
    let start_input = Input::new(&input[offset..]).anchored(Anchored::Yes);
    let mut state = rule
        .dfa
        .start_state_forward(&start_input)
        .map_err(|error| LexError::Engine {
            offset,
            reason: error.to_string(),
        })?;
    let mut position = offset;
    let mut path = Vec::<((usize, StateID), Option<usize>)>::new();

    let mut result = loop {
        if let Some(cached) = memo.get(&(position, state)) {
            break *cached;
        }
        if position == input.len() {
            let state = rule.dfa.next_eoi_state(state);
            break rule.dfa.is_match_state(state).then_some(position);
        }

        let next = rule.dfa.next_state(state, input[position]);
        let matched = rule.dfa.is_match_state(next).then_some(position);
        path.push(((position, state), matched));
        if rule.dfa.is_dead_state(next) {
            break None;
        }
        if rule.dfa.is_quit_state(next) {
            return Err(LexError::Engine {
                offset: position,
                reason: format!("DFA quit on byte {}", input[position]),
            });
        }
        position += 1;
        state = next;
    };

    let retain_path = path.len() >= 256 || !memo.is_empty();
    while let Some((key, matched)) = path.pop() {
        // This mirrors regex-automata's leftmost search: retain the most
        // recent match unless no later transition matched. Greedy, lazy, and
        // ordered-alternation priority are encoded in the DFA.
        result = result.or(matched);
        if retain_path {
            memo.insert(key, result);
        }
    }
    Ok(result)
}

fn better_match(left: Option<LexMatch>, right: Option<LexMatch>) -> Option<LexMatch> {
    match (left, right) {
        (None, other) | (other, None) => other,
        (Some(left), Some(right)) => Some(
            if (left.end, std::cmp::Reverse(left.rule))
                >= (right.end, std::cmp::Reverse(right.rule))
            {
                left
            } else {
                right
            },
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::{Action, parse_action};

    #[test]
    fn action_parser_is_deliberately_small() {
        assert!(matches!(
            parse_action("Leaf()").unwrap(),
            Action::Construct { arguments, .. } if arguments.is_empty()
        ));
        assert!(matches!(
            parse_action("Pair(1, 3)").unwrap(),
            Action::Construct { arguments, .. } if arguments == [1, 3]
        ));
        assert_eq!(parse_action("$1").unwrap(), Action::Project { position: 1 });
        assert!(parse_action("Pair(2, 1)").is_err());
        assert!(parse_action("arbitrary rust() + 1").is_err());
    }
}
