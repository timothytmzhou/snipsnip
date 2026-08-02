use prefixspace::{Grammar, Monitor};

#[test]
fn interleaved_lexemes_and_child_unions_propagate_through_nested_constructors() {
    let grammar = Grammar::from_yacc(
        r#"
        %start start
        %token Y Z
        %%
        start: pair { Outer(1) };
        pair: y z { Pair(1, 2) };
        y: Y { Y() };
        z: Z { Z() };
        "#,
    )
    .unwrap();
    let mut monitor = Monitor::new(
        &grammar,
        r#"
        (datatype Ast
          (Y) (Z) (ExpectedY) (ExpectedZ)
          (Pair Ast Ast)
          (Outer Ast))
        (let $expected-y (ExpectedY))
        (let $expected-z (ExpectedZ))
        (let $root (Outer (Pair $expected-y $expected-z)))
        "#,
        "$root",
    )
    .unwrap();

    assert_eq!(monitor.realizability(), None);
    assert_eq!(monitor.push_token_name("Y", "y").unwrap(), None);

    assert_eq!(monitor.run_egglog("(union $expected-y (Y))").unwrap(), None);
    assert_eq!(monitor.push_token_name("Z", "z").unwrap(), None);

    assert_eq!(
        monitor.run_egglog("(union $expected-z (Z))").unwrap(),
        Some(true)
    );
    assert_eq!(monitor.realizability(), Some(true));
}
