use prefixspace::Grammar;

const YACC: &str = r#"
%start start
%token LET IN ID EQ INT PLUS MINUS STAR SLASH LPAREN RPAREN
%%
start: scoped                         { $1 }
     ;
scoped: add                           { $1 }
      | LET id EQ add IN scoped       { Let(2, 4, 6) }
      ;
add: mul                              { $1 }
   | add PLUS mul                     { Add(1, 3) }
   | add MINUS mul                    { Sub(1, 3) }
   ;
mul: app                              { $1 }
   | mul STAR app                     { Mul(1, 3) }
   | mul SLASH app                    { Div(1, 3) }
   ;
app: atom                             { $1 }
   | app non_neg_atom                 { App(1, 2) }
   ;
atom: non_neg_atom                    { $1 }
    | MINUS atom                      { Neg(2) }
    ;
non_neg_atom: id                      { $1 }
            | num                     { $1 }
            | LPAREN add RPAREN       { $2 }
            ;
id: ID                                { Var(1) }
  ;
num: INT                              { Num(1) }
   ;
"#;

const LEX: &str = r#"
%%
let                        'LET'
in                         'IN'
=                          'EQ'
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

pub fn grammar() -> Grammar {
    Grammar::from_yacc_lex(YACC, LEX).unwrap()
}
