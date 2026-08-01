// Fixed-e-graph cases adapted from ChopChop's `tests/test_egraph.py` and
// `experiments/egraph/benchmarks/*.egglog` at commit
// 681083a6fd921ac9cbaf984db628cf92eb019a3f (MIT).
//
// ChopChop checks after every character. This crate consumes already-lexed
// input, so every assertion below is made at epsilon and after each complete
// lexeme. See THIRD_PARTY_NOTICES.md for attribution and license text.

use prefixspace::{Grammar, LivePrefixMonitor};

const EXPRESSION_YACC: &str = r#"
%start expr
%token PLUS MINUS STAR SLASH LPAREN RPAREN ID INT
%%
expr: add                         { $1 }
    ;
add: mul                          { $1 }
   | add PLUS mul                 { Add(1, 3) }
   | add MINUS mul                { Sub(1, 3) }
   ;
mul: app                          { $1 }
   | mul STAR app                 { Mul(1, 3) }
   | mul SLASH app                { Div(1, 3) }
   ;
app: atom                         { $1 }
   | app non_neg_atom             { App(1, 2) }
   ;
atom: non_neg_atom                { $1 }
    | MINUS atom                  { Neg(2) }
    ;
non_neg_atom: id                  { $1 }
            | num                 { $1 }
            | LPAREN add RPAREN   { $2 }
            ;
id: ID                            { Var(1) }
  ;
num: INT                          { Num(1) }
   ;
"#;

const EXPRESSION_LEX: &str = r#"
%%
\+                         'PLUS'
-                          'MINUS'
\*                         'STAR'
/                          'SLASH'
\(                         'LPAREN'
\)                         'RPAREN'
[0-9]+                     'INT'
[a-zA-Z_][a-zA-Z0-9_]*     'ID'
[ \t\r\n]+                 ;
"#;

// This is ChopChop's `experiments/egraph/let.egglog`, with `$` added to
// egglog 2 global bindings/references. Local rewrite variables remain bare.
const EGRAPH_BASE: &str = r#"
(datatype Math
  (Num i64)
  (Str String)
  (Var String)
  (Add Math Math)
  (Sub Math Math)
  (Neg Math)
  (Pow Math Math)
  (Sqrt Math)
  (Mul Math Math)
  (Div Math Math)
  (App Math Math))

(rewrite (Add a b) (Add b a))
(rewrite (Add (Num a) (Num b)) (Num (+ a b)))
(rewrite (Add (Add a b) c) (Add a (Add b c)))

(rewrite (Neg a) (Sub (Num 0) a))
(rewrite (Sub (Num 0) a) (Neg a))
(rewrite (Sub a b) (Add a (Neg b)))
(rewrite (Sub (Num a) (Num b)) (Num (- a b)))

(rewrite (Mul a b) (Mul b a))
(rewrite (Mul (Num a) (Num b)) (Num (* a b)))
(rewrite (Mul (Mul a b) c) (Mul a (Mul b c)))

(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))

(rewrite (Div a b) (Mul a (Div (Num 1) b)))
(rewrite (Mul a (Div (Num 1) b)) (Div a b))
(rewrite (Div (Num 1) (Mul b c))
         (Mul (Div (Num 1) b) (Div (Num 1) c)))
(rewrite (Mul (Div (Num 1) b) (Div (Num 1) c))
         (Div (Num 1) (Mul b c)))

(let $pow (Var "pow"))
(let $sqrt (Var "sqrt"))

(rewrite (Pow a b) (App (App $pow a) b))
(rewrite (App (App $pow a) b) (Pow a b))
(rewrite (Sqrt a) (App $sqrt a))
(rewrite (App $sqrt a) (Sqrt a))
(rewrite (Pow (Sub a b) (Num 2)) (Pow (Sub b a) (Num 2)))
"#;

const SIX_FIXTURE: &str = r#"
(let $six (Num 6))
(let $times (Mul (Num 3) (Num 2)))
(let $add (Add (Num 3) (Num 3)))
(let $div (Div (Num 6) (Num 1)))
(rewrite (Num 6) (Var "x"))
"#;

const DIVISION_FIXTURE: &str = r#"
(let $div (Div (Mul (Var "a") (Var "b"))
               (Mul (Var "c") (Var "d"))))
"#;

struct Benchmark {
    name: &'static str,
    header: &'static str,
    fixture: &'static str,
}

const BENCHMARKS: &[Benchmark] = &[
    Benchmark {
        name: "auth",
        header: "fetch_document (authorize_user_for_document (authenticate_user current_user web_request) document_id)",
        fixture: r#"
(let $current_user (Var "current_user"))
(let $web_request (Var "web_request"))
(let $document_id (Var "document_id"))
(let $authenticate_user (Var "authenticate_user"))
(let $authorize_user_for_document (Var "authorize_user_for_document"))
(let $fetch_document (Var "fetch_document"))

(let $start
  (App $fetch_document
    (App (App $authorize_user_for_document
          (App (App $authenticate_user $current_user) $web_request))
         $document_id)))
"#,
    },
    Benchmark {
        name: "distance",
        header: "sqrt (pow (x1 - x2) 2 + pow (y1 - y2) 2)",
        fixture: r#"
(let $x1 (Var "x1"))
(let $x2 (Var "x2"))
(let $y1 (Var "y1"))
(let $y2 (Var "y2"))

(let $start (App $sqrt
  (Add
    (App (App $pow (Sub $x1 $x2)) (Num 2))
    (App (App $pow (Sub $y1 $y2)) (Num 2)))))
"#,
    },
    Benchmark {
        name: "gravity",
        header: "pow 10 (-15) * (66743 * m1 * m2) / (pow r 2)",
        fixture: r#"
(let $m1 (Var "m1"))
(let $m2 (Var "m2"))
(let $r (Var "r"))

(let $start
  (Mul
    (Pow (Num 10) (Neg (Num 15)))
    (Div
      (Mul (Mul (Num 66743) $m1) $m2)
      (Pow $r (Num 2)))))
"#,
    },
    Benchmark {
        name: "image",
        header: "add_watermark (apply_filter (crop_image original_image selection) filter_type) watermark_image",
        fixture: r#"
(let $original_image (Var "original_image"))
(let $selection (Var "selection"))
(let $filter_type (Var "filter_type"))
(let $watermark_image (Var "watermark_image"))
(let $crop_image (Var "crop_image"))
(let $apply_filter (Var "apply_filter"))
(let $add_watermark (Var "add_watermark"))

(let $start
  (App (App $add_watermark
        (App (App $apply_filter
              (App (App $crop_image $original_image) $selection))
             $filter_type))
       $watermark_image))
"#,
    },
    Benchmark {
        name: "lerp",
        header: "start + (end - start) * scale",
        fixture: r#"
(let $orig_start (Var "start"))
(let $orig_end (Var "end"))
(let $scale (Var "scale"))

(let $start
  (Add $orig_start
       (Mul (Sub $orig_end $orig_start)
            $scale)))
"#,
    },
    Benchmark {
        name: "positives",
        header: "(sum (filter positive xs)) / (length (filter positive xs))",
        fixture: r#"
(let $xs (Var "xs"))
(let $positive (Var "positive"))
(let $filter (Var "filter"))
(let $sum (Var "sum"))
(let $length (Var "length"))

(let $filtered (App (App $filter $positive) $xs))

(let $start
  (Div
    (App $sum $filtered)
    (App $length $filtered)))
"#,
    },
    Benchmark {
        name: "power",
        header: "power / 1000 * hours * price_per_kwh",
        fixture: r#"
(let $power (Var "power"))
(let $hours (Var "hours"))
(let $price_per_kwh (Var "price_per_kwh"))

(let $start
  (Mul
    (Mul (Div $power (Num 1000)) $hours)
    $price_per_kwh))
"#,
    },
    Benchmark {
        name: "quadratic",
        header: "(-b + sqrt ((pow b 2) - 4 * a * c)) / (2 * a)",
        fixture: r#"
(let $a (Var "a"))
(let $b (Var "b"))
(let $c (Var "c"))

(let $start
  (Div
    (Add
      (Sub (Num 0) $b)
      (App $sqrt
        (Sub
          (App (App $pow $b) (Num 2))
          (Mul (Mul (Num 4) $a) $c))))
    (Mul (Num 2) $a)))
"#,
    },
    Benchmark {
        name: "uppercase",
        header: "map toUpper (filter isAlpha s)",
        fixture: r#"
(let $s (Var "s"))
(let $toUpper (Var "toUpper"))
(let $isAlpha (Var "isAlpha"))
(let $map (Var "map"))
(let $filter (Var "filter"))

(let $filtered (App (App $filter $isAlpha) $s))

(let $start (App (App $map $toUpper) $filtered))
"#,
    },
    Benchmark {
        name: "variance",
        header: "sqrt ((pow (a - ((a+b+c)/3)) 2) + (pow (b - ((a+b+c)/3)) 2) + (pow (c - ((a+b+c)/3)) 2)) / 3",
        fixture: r#"
(let $a (Var "a"))
(let $b (Var "b"))
(let $c (Var "c"))

(let $start
  (Div
    (App $sqrt
      (Add
        (Add
          (App (App $pow
            (Sub $a (Div (Add (Add $a $b) $c) (Num 3))))
            (Num 2))
          (App (App $pow
            (Sub $b (Div (Add (Add $a $b) $c) (Num 3))))
            (Num 2)))
        (App (App $pow
          (Sub $c (Div (Add (Add $a $b) $c) (Num 3))))
          (Num 2))))
    (Num 3)))
"#,
    },
];

fn expression_grammar() -> Grammar {
    Grammar::from_yacc_lex(EXPRESSION_YACC, EXPRESSION_LEX).unwrap()
}

fn egraph_program(fixture: &str) -> String {
    format!("{EGRAPH_BASE}\n{fixture}\n(run 100)\n")
}

fn assert_lexeme_trace(
    grammar: &Grammar,
    program: &str,
    target: &str,
    source: &str,
    expected_viable: &[bool],
    case: &str,
) {
    let tokens = grammar.lex(source).unwrap();
    assert_eq!(
        expected_viable.len(),
        tokens.len() + 1,
        "bad expected trace for {case}: {source:?}"
    );

    let mut monitor = LivePrefixMonitor::from_egglog(grammar, program, target)
        .unwrap_or_else(|error| panic!("could not build {case} monitor: {error}"));
    assert_eq!(
        !monitor.intersection_is_empty(),
        expected_viable[0],
        "{case}: viability mismatch at epsilon for {source:?}"
    );

    for (index, token) in tokens.iter().enumerate() {
        let terminal = grammar.terminal_name(token.kind);
        let empty = monitor
            .push_token_name(terminal, &token.lexeme)
            .unwrap_or_else(|error| {
                panic!(
                    "{case}: failed to push {terminal} {:?} in {source:?}: {error}",
                    token.lexeme
                )
            });
        assert_eq!(
            !empty,
            expected_viable[index + 1],
            "{case}: viability mismatch after lexeme {} ({terminal} {:?}), prefix {:?}",
            index + 1,
            token.lexeme,
            &source[..token.end]
        );
    }
}

fn assert_all_lexeme_prefixes_viable(
    grammar: &Grammar,
    program: &str,
    target: &str,
    source: &str,
    case: &str,
) {
    let token_count = grammar.lex(source).unwrap().len();
    assert_lexeme_trace(
        grammar,
        program,
        target,
        source,
        &vec![true; token_count + 1],
        case,
    );
}

#[test]
fn chopchop_static_six_oracle_at_lexeme_boundaries() {
    let grammar = expression_grammar();
    let program = egraph_program(SIX_FIXTURE);

    for source in ["", "6", "3 * 2", "3 *", "3 + ", "x"] {
        assert_all_lexeme_prefixes_viable(&grammar, &program, "$six", source, "static-six");
    }

    // At lexeme granularity these are epsilon=true, first operand=true,
    // operator=false. Whitespace does not create a boundary in this port.
    assert_lexeme_trace(
        &grammar,
        &program,
        "$six",
        "2 +",
        &[true, true, false],
        "static-six",
    );
    assert_lexeme_trace(
        &grammar,
        &program,
        "$six",
        "x +",
        &[true, true, false],
        "static-six",
    );
}

#[test]
fn chopchop_division_oracle_at_lexeme_boundaries() {
    let grammar = expression_grammar();
    let program = egraph_program(DIVISION_FIXTURE);

    for source in [
        "(a * b) / (c * d)",
        "(a * b) * (1 / (c * d))",
        "a * (b / (c * d))",
        "(a / c) * (b / d)",
    ] {
        assert_all_lexeme_prefixes_viable(&grammar, &program, "$div", source, "division");
    }

    assert_lexeme_trace(&grammar, &program, "$div", "c", &[true, false], "division");
}

#[test]
fn chopchop_benchmark_headers_at_every_lexeme_boundary() {
    let grammar = expression_grammar();

    for benchmark in BENCHMARKS {
        let program = egraph_program(benchmark.fixture);
        assert_all_lexeme_prefixes_viable(
            &grammar,
            &program,
            "$start",
            benchmark.header,
            benchmark.name,
        );
    }
}
