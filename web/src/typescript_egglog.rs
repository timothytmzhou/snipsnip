//! Standalone Egglog program for the TypeScript subset used by the web demo.
//!
//! This module deliberately contains no parsing or streaming integration. The
//! program consumes concrete `Goal` terms and classifies them by equality with
//! `Accept` or `Reject`.

pub const DEFAULT_EGGLOG_PROGRAM: &str = r#"
(datatype Expr
  (NumberLiteral)
  (StringLiteral)
  (TrueLiteral)
  (FalseLiteral)
  (Add Expr Expr)
  (Subtract Expr Expr)
  (Multiply Expr Expr)
  (Divide Expr Expr)
  (Modulo Expr Expr)
  (LessThan Expr Expr)
  (Property Expr String)
  (Identifier String)
  (Call Expr Expr)
  ;; These five constructors are analysis results, never parser actions.
  (NumberExpression)
  (StringExpression)
  (BooleanExpression)
  (NumberFunctionExpression)
  (ExpressionError))

(datatype Annotation
  (NumberAnnotation)
  (StringAnnotation)
  (BooleanAnnotation))

(datatype Declaration
  (LetDeclaration Annotation Expr))

(datatype Goal
  (Analyze Declaration)
  (Accept)
  (Reject))

;; A negative answer requires an explicit proof. Raw Analyze terms are not
;; declared disjoint from Accept: without typing rules the answer is Unknown.
(relation Disjoint (Goal Goal))
(Disjoint (Reject) (Accept))
(let $required (Accept))

;; TypeScript typing rules (primitive strict-mode subset).
;; Literal spelling is deliberately absent from the AST because it cannot
;; affect any rule in this type-only analysis.
(birewrite (NumberLiteral) (NumberExpression))
(birewrite (StringLiteral) (StringExpression))
(birewrite (TrueLiteral) (BooleanExpression))
(birewrite (FalseLiteral) (BooleanExpression))

;; TypeScript's global Number function converts every primitive value in this
;; subset to a number. The call birewrite gives NumberExpression a cyclic
;; representative during initial saturation, so nested Number(...) syntax
;; reuses one closed e-class at every depth.
(birewrite (Identifier "Number") (NumberFunctionExpression))
(birewrite
  (Call (NumberFunctionExpression) (NumberExpression))
  (NumberExpression))
(rewrite
  (Call (NumberFunctionExpression) (StringExpression))
  (NumberExpression))
(rewrite
  (Call (NumberFunctionExpression) (BooleanExpression))
  (NumberExpression))
(rewrite
  (Call (NumberFunctionExpression) (NumberFunctionExpression))
  (NumberExpression))

;; Numeric arithmetic.
(birewrite (Subtract (NumberExpression) (NumberExpression)) (NumberExpression))
(birewrite (Multiply (NumberExpression) (NumberExpression)) (NumberExpression))
(birewrite (Divide (NumberExpression) (NumberExpression)) (NumberExpression))
(birewrite (Modulo (NumberExpression) (NumberExpression)) (NumberExpression))

;; TypeScript + is numeric for two numbers and string concatenation whenever
;; either operand is a string. Other primitive pairs are errors.
(birewrite (Add (NumberExpression) (NumberExpression)) (NumberExpression))
(birewrite (Add (StringExpression) (NumberExpression)) (StringExpression))
(birewrite (Add (StringExpression) (StringExpression)) (StringExpression))
(birewrite (Add (StringExpression) (BooleanExpression)) (StringExpression))
(birewrite (Add (NumberExpression) (StringExpression)) (StringExpression))
(birewrite (Add (BooleanExpression) (StringExpression)) (StringExpression))
(rewrite (Add (NumberExpression) (BooleanExpression)) (ExpressionError))
(rewrite (Add (BooleanExpression) (NumberExpression)) (ExpressionError))
(rewrite (Add (BooleanExpression) (BooleanExpression)) (ExpressionError))

;; Numeric-only operators reject string and boolean operands.
(rewrite (Subtract (StringExpression) other) (ExpressionError))
(rewrite (Subtract other (StringExpression)) (ExpressionError))
(rewrite (Subtract (BooleanExpression) other) (ExpressionError))
(rewrite (Subtract other (BooleanExpression)) (ExpressionError))
(rewrite (Multiply (StringExpression) other) (ExpressionError))
(rewrite (Multiply other (StringExpression)) (ExpressionError))
(rewrite (Multiply (BooleanExpression) other) (ExpressionError))
(rewrite (Multiply other (BooleanExpression)) (ExpressionError))
(rewrite (Divide (StringExpression) other) (ExpressionError))
(rewrite (Divide other (StringExpression)) (ExpressionError))
(rewrite (Divide (BooleanExpression) other) (ExpressionError))
(rewrite (Divide other (BooleanExpression)) (ExpressionError))
(rewrite (Modulo (StringExpression) other) (ExpressionError))
(rewrite (Modulo other (StringExpression)) (ExpressionError))
(rewrite (Modulo (BooleanExpression) other) (ExpressionError))
(rewrite (Modulo other (BooleanExpression)) (ExpressionError))

;; Relational results. This subset accepts number/number and string/string;
;; TypeScript rejects boolean operands and mixed primitive domains.
(birewrite (LessThan (NumberExpression) (NumberExpression)) (BooleanExpression))
(birewrite (LessThan (StringExpression) (StringExpression)) (BooleanExpression))
(rewrite (LessThan (BooleanExpression) other) (ExpressionError))
(rewrite (LessThan other (BooleanExpression)) (ExpressionError))
(rewrite (LessThan (NumberExpression) (StringExpression)) (ExpressionError))
(rewrite (LessThan (StringExpression) (NumberExpression)) (ExpressionError))
(rewrite (LessThan (NumberExpression) (BooleanExpression)) (ExpressionError))
(rewrite (LessThan (BooleanExpression) (NumberExpression)) (ExpressionError))
(rewrite (LessThan (StringExpression) (BooleanExpression)) (ExpressionError))
(rewrite (LessThan (BooleanExpression) (StringExpression)) (ExpressionError))

;; Only strings have `.length` in this subset. `length` remains an ordinary
;; identifier everywhere else in the grammar.
(birewrite (Property (StringExpression) "length") (NumberExpression))
(rewrite (Property (NumberExpression) "length") (ExpressionError))
(rewrite (Property (BooleanExpression) "length") (ExpressionError))
(rewrite (Property expression property) (ExpressionError) :when ((!= property "length")))

;; An error is poison through every enclosing expression constructor.
(rewrite (Add (ExpressionError) other) (ExpressionError))
(rewrite (Add other (ExpressionError)) (ExpressionError))
(rewrite (Subtract (ExpressionError) other) (ExpressionError))
(rewrite (Subtract other (ExpressionError)) (ExpressionError))
(rewrite (Multiply (ExpressionError) other) (ExpressionError))
(rewrite (Multiply other (ExpressionError)) (ExpressionError))
(rewrite (Divide (ExpressionError) other) (ExpressionError))
(rewrite (Divide other (ExpressionError)) (ExpressionError))
(rewrite (Modulo (ExpressionError) other) (ExpressionError))
(rewrite (Modulo other (ExpressionError)) (ExpressionError))
(rewrite (LessThan (ExpressionError) other) (ExpressionError))
(rewrite (LessThan other (ExpressionError)) (ExpressionError))
(rewrite (Property (ExpressionError) property) (ExpressionError))

;; Assignment compatibility for primitive annotations.
(birewrite (Analyze (LetDeclaration (NumberAnnotation) (NumberExpression))) (Accept))
(birewrite (Analyze (LetDeclaration (StringAnnotation) (StringExpression))) (Accept))
(birewrite (Analyze (LetDeclaration (BooleanAnnotation) (BooleanExpression))) (Accept))
(rewrite (Analyze (LetDeclaration (NumberAnnotation) (StringExpression))) (Reject))
(rewrite (Analyze (LetDeclaration (NumberAnnotation) (BooleanExpression))) (Reject))
(rewrite (Analyze (LetDeclaration (StringAnnotation) (NumberExpression))) (Reject))
(rewrite (Analyze (LetDeclaration (StringAnnotation) (BooleanExpression))) (Reject))
(rewrite (Analyze (LetDeclaration (BooleanAnnotation) (NumberExpression))) (Reject))
(rewrite (Analyze (LetDeclaration (BooleanAnnotation) (StringExpression))) (Reject))
(rewrite (Analyze (LetDeclaration annotation (NumberFunctionExpression))) (Reject))
(rewrite (Analyze (LetDeclaration annotation (ExpressionError))) (Reject))
"#;
