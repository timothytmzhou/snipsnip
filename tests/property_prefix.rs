use prefixspace::{Grammar, PrefixMonitor, RegularTreeGrammar};
use proptest::prelude::*;

const GRAMMAR: &str = r#"
%start start
%token ZERO ONE BANG
%%
start: bits BANG { Even(1) };
bits: ZERO bits { Flip(2) }
    | ONE bits { Same(2) }
    | { Zero() }
    ;
"#;

const EGRAPH: &str = r#"
(datatype Ast (Even Ast) (Zero) (Flip Ast) (Same Ast))
(let $even-zero (Zero))
(union (Same $even-zero) $even-zero)
(let $odd (Flip $even-zero))
(union (Same $odd) $odd)
(union (Flip $odd) $even-zero)
(let $root (Even $even-zero))
"#;

// This independently computes the quotient state of the right-recursive bit AST.
fn accepted_complete_word(word: &str) -> bool {
    let Some(bits) = word.strip_suffix('!') else {
        return false;
    };
    bits.bytes().all(|byte| matches!(byte, b'0' | b'1'))
        && bits.bytes().filter(|byte| *byte == b'0').count() % 2 == 0
}

fn brute_has_completion(prefix: &str, max_more_bits: usize) -> bool {
    if prefix.contains('!') {
        return accepted_complete_word(prefix);
    }
    (0..=max_more_bits).any(|count| {
        (0usize..(1usize << count)).any(|mask| {
            let mut word = String::from(prefix);
            for bit in 0..count {
                word.push(if mask & (1 << bit) == 0 { '0' } else { '1' });
            }
            word.push('!');
            accepted_complete_word(&word)
        })
    })
}

proptest! {
    #[test]
    fn streaming_result_matches_bounded_exhaustive_semantics(
        input in prop::collection::vec(prop_oneof![Just('0'), Just('1'), Just('!')], 0..10)
    ) {
        let grammar = Grammar::from_yacc(GRAMMAR).unwrap();
        let (automaton, target) =
            RegularTreeGrammar::from_egglog(EGRAPH, "$root").unwrap();
        let mut stream = PrefixMonitor::compile(&grammar, &automaton, target).unwrap();
        let mut prefix = String::new();
        prop_assert_eq!(stream.has_completion(), brute_has_completion("", 2));
        for character in input {
            prefix.push(character);
            let terminal = match character {
                '0' => "ZERO",
                '1' => "ONE",
                '!' => "BANG",
                _ => unreachable!(),
            };
            let empty = stream.push_token_name(terminal).unwrap();
            prop_assert_eq!(!empty, brute_has_completion(&prefix, 2), "prefix={:?}", prefix);
        }
    }
}
