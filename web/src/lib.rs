use prefixspace::{Grammar, GrammarError, Monitor, MonitorError, TerminalId, Token};
use serde::Serialize;
use thiserror::Error;
use web_time::Instant;

mod typescript_egglog;

pub use typescript_egglog::DEFAULT_EGGLOG_PROGRAM;

pub const TYPESCRIPT_YACC: &str = r#"
%start goal
%token LET IDENT COLON NUMBER_TYPE STRING_TYPE BOOLEAN_TYPE EQ
%token NUM STRING_LITERAL TRUE FALSE
%token PLUS MINUS STAR SLASH PERCENT LT DOT
%token LPAREN RPAREN SEMI
%%
goal: declaration                                      { Analyze(1) };
declaration: LET IDENT COLON annotation EQ expression SEMI { LetDeclaration(4, 6) };
annotation: NUMBER_TYPE                                { NumberAnnotation() }
          | STRING_TYPE                                { StringAnnotation() }
          | BOOLEAN_TYPE                               { BooleanAnnotation() }
          ;
expression: relational                                 { $1 };
relational: additive                                   { $1 }
          | relational LT additive                     { LessThan(1, 3) }
          ;
additive: multiplicative                               { $1 }
        | additive PLUS multiplicative                 { Add(1, 3) }
        | additive MINUS multiplicative                { Subtract(1, 3) }
        ;
multiplicative: postfix                                { $1 }
              | multiplicative STAR postfix            { Multiply(1, 3) }
              | multiplicative SLASH postfix           { Divide(1, 3) }
              | multiplicative PERCENT postfix         { Modulo(1, 3) }
              ;
postfix: primary                                       { $1 }
       | postfix DOT IDENT                             { Property(1, 3) }
       | postfix LPAREN expression RPAREN              { Call(1, 3) }
       ;
primary: NUM                                           { NumberLiteral() }
       | STRING_LITERAL                                { StringLiteral() }
       | TRUE                                          { TrueLiteral() }
       | FALSE                                         { FalseLiteral() }
       | IDENT                                         { Identifier(1) }
       | LPAREN expression RPAREN                      { $2 }
       ;
"#;

pub const TYPESCRIPT_LEX: &str = r#"
%%
let                          'LET'
number                       'NUMBER_TYPE'
string                       'STRING_TYPE'
boolean                      'BOOLEAN_TYPE'
true                         'TRUE'
false                        'FALSE'
[0-9]+                       'NUM'
\"([^\"\\]|\\.)*\"|'([^'\\]|\\.)*' 'STRING_LITERAL'
[A-Za-z_][A-Za-z0-9_]*       'IDENT'
:                            'COLON'
=                            'EQ'
\+                           'PLUS'
-                            'MINUS'
\*                           'STAR'
/                            'SLASH'
%                            'PERCENT'
\<                           'LT'
\.                           'DOT'
\(                           'LPAREN'
\)                           'RPAREN'
;                            'SEMI'
[ \t\r\n]+                   ;
"#;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum RealizabilityState {
    Realizable,
    Unrealizable,
    Unknown,
}

impl From<Option<bool>> for RealizabilityState {
    fn from(value: Option<bool>) -> Self {
        match value {
            Some(true) => Self::Realizable,
            Some(false) => Self::Unrealizable,
            None => Self::Unknown,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TokenAnalysis {
    pub terminal: String,
    pub lexeme: String,
    /// UTF-16 code-unit offset into the analyzed source, matching browser text
    /// selection APIs.
    pub start: usize,
    /// Exclusive UTF-16 code-unit offset into the analyzed source.
    pub end: usize,
    pub elapsed_ms: f64,
    pub realizability: RealizabilityState,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AnalysisReport {
    pub tokens: Vec<TokenAnalysis>,
    pub realizability: RealizabilityState,
    pub total_ms: f64,
    pub incremental: bool,
}

#[derive(Debug, Error)]
pub enum AnalyzerError {
    #[error(transparent)]
    Grammar(#[from] GrammarError),
    #[error(transparent)]
    Monitor(#[from] MonitorError),
    #[error("could not serialize analysis report: {0}")]
    Serialize(#[from] serde_json::Error),
}

struct CachedToken {
    kind: TerminalId,
    analysis: TokenAnalysis,
}

struct Session {
    monitor: Monitor,
    tokens: Vec<CachedToken>,
}

/// Stateful analyzer used by both native tests and the browser wrapper.
pub struct TypeScriptAnalyzer {
    grammar: Grammar,
    program: String,
    session: Option<Session>,
    has_analyzed: bool,
}

impl TypeScriptAnalyzer {
    /// Creates an analyzer and validates that `program` defines `$required`,
    /// `Disjoint`, and all constructors used by the TypeScript grammar.
    pub fn new(program: impl Into<String>) -> Result<Self, AnalyzerError> {
        let grammar = Grammar::from_yacc_lex(TYPESCRIPT_YACC, TYPESCRIPT_LEX)?;
        let program = program.into();
        let session = Some(new_session(&grammar, &program)?);
        Ok(Self {
            grammar,
            program,
            session,
            has_analyzed: false,
        })
    }

    /// Analyzes exactly `source`. The caller is responsible for withholding a
    /// trailing incomplete lexeme.
    ///
    /// If its token stream extends the preceding successful analysis, only
    /// the new tokens are pushed into the retained monitor. Otherwise a fresh
    /// monitor is built from the configured egglog program.
    pub fn analyze(&mut self, source: &str) -> Result<AnalysisReport, AnalyzerError> {
        let total_started = Instant::now();
        let tokens = self.grammar.lex(source)?;
        let spans = utf16_spans(source, &tokens);
        let had_previous_analysis = self.has_analyzed;
        let previous = self.session.take();
        let extends_previous = previous
            .as_ref()
            .is_some_and(|session| token_stream_extends(&session.tokens, &tokens));
        let mut session = if extends_previous {
            previous.expect("extension was checked against this session")
        } else {
            new_session(&self.grammar, &self.program)?
        };

        // Spans belong to the current source rather than to the semantic token
        // stream. Whitespace-only edits may move a reused token without making
        // the monitor replay it.
        for ((cached, token), &(start, end)) in session.tokens.iter_mut().zip(&tokens).zip(&spans) {
            debug_assert_eq!(cached.kind, token.kind);
            debug_assert_eq!(cached.analysis.lexeme, token.lexeme);
            cached.analysis.start = start;
            cached.analysis.end = end;
        }

        for (token, &(start, end)) in tokens[session.tokens.len()..]
            .iter()
            .zip(&spans[session.tokens.len()..])
        {
            let token_started = Instant::now();
            session.monitor.push_token(token)?;
            let elapsed_ms = milliseconds(token_started);
            session.tokens.push(CachedToken {
                kind: token.kind,
                analysis: TokenAnalysis {
                    terminal: self.grammar.terminal_name(token.kind).to_owned(),
                    lexeme: token.lexeme.clone(),
                    start,
                    end,
                    elapsed_ms,
                    realizability: session.monitor.realizability().into(),
                },
            });
        }

        let report = AnalysisReport {
            tokens: session
                .tokens
                .iter()
                .map(|token| token.analysis.clone())
                .collect(),
            realizability: session.monitor.realizability().into(),
            total_ms: milliseconds(total_started),
            incremental: had_previous_analysis && extends_previous,
        };
        self.session = Some(session);
        self.has_analyzed = true;
        Ok(report)
    }

    pub fn analyze_json(&mut self, source: &str) -> Result<String, AnalyzerError> {
        Ok(serde_json::to_string(&self.analyze(source)?)?)
    }

    pub fn reset(&mut self) -> Result<(), AnalyzerError> {
        let session = new_session(&self.grammar, &self.program)?;
        self.session = Some(session);
        self.has_analyzed = false;
        Ok(())
    }

    /// Atomically replaces the editable egglog setup and clears the stream.
    /// The old setup remains active if validation fails.
    pub fn set_program(&mut self, program: impl Into<String>) -> Result<(), AnalyzerError> {
        let program = program.into();
        let session = new_session(&self.grammar, &program)?;
        self.program = program;
        self.session = Some(session);
        self.has_analyzed = false;
        Ok(())
    }

    pub fn program(&self) -> &str {
        &self.program
    }
}

fn new_session(grammar: &Grammar, program: &str) -> Result<Session, AnalyzerError> {
    Ok(Session {
        monitor: Monitor::new(grammar, program, "$required")?,
        tokens: Vec::new(),
    })
}

fn token_stream_extends(previous: &[CachedToken], current: &[Token]) -> bool {
    previous.len() <= current.len()
        && previous.iter().zip(current).all(|(old, new)| {
            old.kind == new.kind && old.analysis.lexeme.as_str() == new.lexeme.as_str()
        })
}

/// Converts the lexer's sorted, non-overlapping UTF-8 byte spans in one pass.
fn utf16_spans(source: &str, tokens: &[Token]) -> Vec<(usize, usize)> {
    let mut byte_cursor = 0;
    let mut utf16_cursor = 0;
    let mut advance = |target: usize| {
        debug_assert!(target >= byte_cursor);
        utf16_cursor += source[byte_cursor..target]
            .chars()
            .map(char::len_utf16)
            .sum::<usize>();
        byte_cursor = target;
        utf16_cursor
    };

    tokens
        .iter()
        .map(|token| {
            let start = advance(token.start);
            let end = advance(token.end);
            (start, end)
        })
        .collect()
}

fn milliseconds(started: Instant) -> f64 {
    started.elapsed().as_secs_f64() * 1_000.0
}

#[cfg(target_arch = "wasm32")]
mod wasm {
    use wasm_bindgen::prelude::*;

    use super::{
        DEFAULT_EGGLOG_PROGRAM, TYPESCRIPT_LEX, TYPESCRIPT_YACC,
        TypeScriptAnalyzer as NativeTypeScriptAnalyzer,
    };

    /// JavaScript export. Own one instance in the worker and call `analyze`
    /// with the debounced, lexically complete source prefix.
    #[wasm_bindgen]
    pub struct TypeScriptAnalyzer {
        inner: NativeTypeScriptAnalyzer,
    }

    #[wasm_bindgen]
    impl TypeScriptAnalyzer {
        #[wasm_bindgen(constructor)]
        pub fn new(program: String) -> Result<TypeScriptAnalyzer, JsValue> {
            NativeTypeScriptAnalyzer::new(program)
                .map(|inner| Self { inner })
                .map_err(js_error)
        }

        /// Returns one JSON-encoded `AnalysisReport`.
        #[wasm_bindgen(js_name = analyze)]
        pub fn analyze_json(&mut self, source: String) -> Result<String, JsValue> {
            self.inner.analyze_json(&source).map_err(js_error)
        }

        pub fn reset(&mut self) -> Result<(), JsValue> {
            self.inner.reset().map_err(js_error)
        }

        #[wasm_bindgen(js_name = setProgram)]
        pub fn set_program(&mut self, program: String) -> Result<(), JsValue> {
            self.inner.set_program(program).map_err(js_error)
        }

        #[wasm_bindgen(js_name = defaultEgglogProgram)]
        pub fn default_egglog_program() -> String {
            DEFAULT_EGGLOG_PROGRAM.to_owned()
        }

        #[wasm_bindgen(js_name = typescriptYacc)]
        pub fn typescript_yacc() -> String {
            TYPESCRIPT_YACC.to_owned()
        }

        #[wasm_bindgen(js_name = typescriptLex)]
        pub fn typescript_lex() -> String {
            TYPESCRIPT_LEX.to_owned()
        }
    }

    fn js_error(error: impl std::fmt::Display) -> JsValue {
        JsValue::from_str(&error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use serde_json::Value;

    use super::{DEFAULT_EGGLOG_PROGRAM, RealizabilityState, TypeScriptAnalyzer};

    #[test]
    fn valid_and_invalid_typescript_prefixes_have_expected_traces() {
        let valid_source = "let answer: number = 42";
        let mut valid = TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM).unwrap();
        let report = valid.analyze(valid_source).unwrap();

        assert!(!report.incremental);
        assert_eq!(report.realizability, RealizabilityState::Realizable);
        assert_eq!(
            report
                .tokens
                .iter()
                .map(|token| token.terminal.as_str())
                .collect::<Vec<_>>(),
            ["LET", "IDENT", "COLON", "NUMBER_TYPE", "EQ", "NUM"]
        );
        assert!(
            report
                .tokens
                .iter()
                .all(|token| token.realizability == RealizabilityState::Realizable)
        );
        for token in &report.tokens {
            assert_eq!(&valid_source[token.start..token.end], token.lexeme);
            assert!(token.elapsed_ms.is_finite() && token.elapsed_ms >= 0.0);
        }
        assert!(report.total_ms.is_finite() && report.total_ms >= 0.0);

        for source in [
            "let answer: number = true;",
            "let answer: number = \"text\";",
        ] {
            let mut invalid = TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM).unwrap();
            let report = invalid.analyze(source).unwrap();
            assert_eq!(report.realizability, RealizabilityState::Unrealizable);
            assert_eq!(report.tokens.last().unwrap().terminal, "SEMI");
            assert_eq!(
                report.tokens.last().unwrap().realizability,
                RealizabilityState::Unrealizable
            );
        }
    }

    #[test]
    fn append_reuses_the_monitor_while_edits_and_reset_rebuild() {
        let mut analyzer = TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM).unwrap();
        let prefix = analyzer.analyze("let x: number = 1").unwrap();
        let appended = analyzer.analyze("let x: number = 1;").unwrap();
        assert!(appended.incremental);
        assert_eq!(
            prefix.tokens,
            appended.tokens[..prefix.tokens.len()],
            "old token results must be retained, not replayed"
        );

        let edited = analyzer.analyze("let x: number = true;").unwrap();
        assert!(!edited.incremental);
        assert_eq!(edited.realizability, RealizabilityState::Unrealizable);

        let unchanged = analyzer.analyze("let x: number = true;").unwrap();
        assert!(unchanged.incremental);

        analyzer.reset().unwrap();
        let after_reset = analyzer.analyze("let x: number = true;").unwrap();
        assert!(!after_reset.incremental);
    }

    #[test]
    fn program_replacement_is_validated_and_forces_a_rebuild() {
        let mut analyzer = TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM).unwrap();
        analyzer.analyze("let x: number = 1").unwrap();

        let alternate =
            DEFAULT_EGGLOG_PROGRAM.replace("(let $required (Accept))", "(let $required (Reject))");
        analyzer.set_program(alternate.clone()).unwrap();
        assert_eq!(analyzer.program(), alternate);
        let report = analyzer.analyze("let x: number = true;").unwrap();
        assert!(!report.incremental);
        assert_eq!(report.realizability, RealizabilityState::Realizable);

        let missing_required = DEFAULT_EGGLOG_PROGRAM.replace("(let $required (Accept))", "");
        let error = analyzer.set_program(missing_required).unwrap_err();
        assert!(error.to_string().contains("required"), "{error}");
        assert_eq!(
            analyzer.program(),
            alternate,
            "failed replacement is atomic"
        );
    }

    #[test]
    fn json_contract_uses_camel_case_and_includes_terminal_names() {
        let mut analyzer = TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM).unwrap();
        let json: Value =
            serde_json::from_str(&analyzer.analyze_json("let x: number = 1").unwrap()).unwrap();
        assert_eq!(json["realizability"], "realizable");
        assert_eq!(json["incremental"], false);
        assert!(json["totalMs"].is_number());
        assert_eq!(json["tokens"][0]["terminal"], "LET");
        assert_eq!(json["tokens"][0]["lexeme"], "let");
        assert!(json["tokens"][0]["elapsedMs"].is_number());
        assert_eq!(json["tokens"][0]["start"], 0);
        assert_eq!(json["tokens"][0]["end"], 3);
    }

    #[test]
    fn token_spans_use_utf16_code_units_for_browser_selection_apis() {
        let source = "let x: number = \"😀\"";
        let mut analyzer = TypeScriptAnalyzer::new(DEFAULT_EGGLOG_PROGRAM).unwrap();
        let report = analyzer.analyze(source).unwrap();
        let literal = report.tokens.last().unwrap();

        assert_eq!(literal.terminal, "STRING_LITERAL");
        assert_eq!(literal.lexeme, "\"😀\"");
        assert_eq!((literal.start, literal.end), (16, 20));
        assert_eq!(source.encode_utf16().count(), 20);
        assert_eq!(
            source.len(),
            22,
            "the regression needs UTF-8 and UTF-16 to differ"
        );
    }
}
