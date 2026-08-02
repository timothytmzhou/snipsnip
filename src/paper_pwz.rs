//! A direct, ID-based transcription of Figures 1 and 2 from
//! *Parsing with Zippers*.
//!
//! This module deliberately contains no lexer, grammar analysis, semantic
//! actions, or backend integration. The maps are the paper's mutable graph;
//! [`Edit`] reports its new monotone semantic relationships after a derivative.

use rustc_hash::FxHashMap as HashMap;

pub type Terminal = u32;
pub type GrammarSymbol = u32;

/// A concrete input token. Matching inspects only `terminal`; the complete
/// payload is retained in the parse expression produced for a match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token<P> {
    pub terminal: Terminal,
    pub payload: P,
}

/// The paper's `sym`, including both grammar labels and consumed tokens.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Symbol<P> {
    Bottom,
    Grammar(GrammarSymbol),
    Token(Token<P>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ExpressionId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MemoId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ContextId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Grammar<P> {
    pub root: ExpressionId,
    pub expressions: HashMap<ExpressionId, ExpressionNode<P>>,
    /// Optional production SELECT sets used only to avoid entering branches
    /// which cannot consume the current terminal. Missing entries mean no
    /// pruning, preserving the paper's general expression interface.
    pub select: HashMap<ExpressionId, Box<[Terminal]>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExpressionNode<P> {
    Tok(Terminal),
    Seq {
        symbol: Symbol<P>,
        children: Vec<ExpressionId>,
    },
    Alt {
        children: Vec<ExpressionId>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Expression<P> {
    pub memo: Option<MemoId>,
    /// False for the cyclic grammar graph; true for a parse fragment fixed by
    /// the consumed prefix.
    pub fixed: bool,
    pub node: ExpressionNode<P>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Context<P> {
    Top,
    Seq {
        memo: MemoId,
        symbol: Symbol<P>,
        /// Completed children in source order. A `Vec` can append efficiently,
        /// unlike the paper's linked list, so no final reversal is needed.
        left: Vec<ExpressionId>,
        right: Vec<ExpressionId>,
    },
    Alt {
        memo: MemoId,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memo {
    pub start: Option<usize>,
    pub parents: Vec<ContextId>,
    pub end: Option<usize>,
    pub result: Option<ExpressionId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Zipper<P> {
    pub focus: ExpressionNode<P>,
    pub memo: MemoId,
}

/// A new monotone semantic relationship produced by one derivative. Consumers
/// read newly named expressions and contexts directly from [`Pwz`]'s maps.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Edit {
    NewExpression(ExpressionId),
    NewContext(ContextId),
    MemoParentAppended {
        memo: MemoId,
        context: ContextId,
    },
    AlternativeChildAppended {
        alternative: ExpressionId,
        child: ExpressionId,
    },
}

pub struct Derivative<'a, P> {
    /// The updated PwZ graph. This lets downstream incremental analyses read
    /// the graph and its edit slice without copying either one.
    pub pwz: &'a Pwz<P>,
    pub zippers: &'a [Zipper<P>],
    pub edits: &'a [Edit],
}

pub struct Pwz<P> {
    pub expressions: HashMap<ExpressionId, Expression<P>>,
    pub memos: HashMap<MemoId, Memo>,
    pub contexts: HashMap<ContextId, Context<P>>,

    pub(crate) zippers: Vec<Zipper<P>>,
    select: HashMap<ExpressionId, Box<[Terminal]>>,
    edits: Vec<Edit>,
    position: usize,
    next_expression: u32,
    next_memo: u32,
    next_context: u32,
}

enum Operation<P> {
    Down {
        context: ContextId,
        expression: ExpressionId,
    },
    DownFresh {
        memo: MemoId,
        node: ExpressionNode<P>,
    },
    Up {
        node: ExpressionNode<P>,
        memo: MemoId,
    },
    UpContext {
        expression: ExpressionId,
        context: ContextId,
    },
}

impl<P: Clone> Pwz<P> {
    /// Builds the special initial zipper from Section 3 of the paper.
    pub fn new(grammar: Grammar<P>) -> Self {
        assert!(
            grammar.expressions.contains_key(&grammar.root),
            "grammar root is absent from the expression map"
        );
        let root_has_completion = !matches!(
            grammar.expressions.get(&grammar.root),
            Some(ExpressionNode::Alt { children }) if children.is_empty()
        );
        for node in grammar.expressions.values() {
            for child in node.children() {
                assert!(
                    grammar.expressions.contains_key(child),
                    "grammar contains a dangling expression ID"
                );
            }
        }

        let next_expression = grammar
            .expressions
            .keys()
            .map(|id| id.0)
            .max()
            .map_or(0, |id| {
                id.checked_add(1).expect("expression ID space exhausted")
            });
        let expressions = grammar
            .expressions
            .into_iter()
            .map(|(id, node)| {
                (
                    id,
                    Expression {
                        memo: None,
                        fixed: false,
                        node,
                    },
                )
            })
            .collect();
        let mut parser = Self {
            expressions,
            memos: HashMap::default(),
            contexts: HashMap::default(),
            zippers: Vec::new(),
            select: grammar.select,
            edits: Vec::new(),
            position: 0,
            next_expression,
            next_memo: 0,
            next_context: 0,
        };

        let top = parser.insert_context(Context::Top);
        let top_memo = parser.insert_memo(None);
        parser.append_parent(top_memo, top);
        let initial_context = parser.insert_context(Context::Seq {
            memo: top_memo,
            symbol: Symbol::Bottom,
            left: Vec::new(),
            right: vec![grammar.root],
        });
        let initial_memo = parser.insert_memo(None);
        parser.append_parent(initial_memo, initial_context);
        if root_has_completion {
            parser.zippers.push(Zipper {
                focus: ExpressionNode::Seq {
                    symbol: Symbol::Bottom,
                    children: Vec::new(),
                },
                memo: initial_memo,
            });
        }

        // `new` exposes the initialized maps directly. `derive` reports only
        // edits made by that derivative.
        parser.edits.clear();
        parser
    }

    /// Takes one derivative of every current zipper, following Figure 1.
    pub fn derive(&mut self, token: Token<P>) -> Derivative<'_, P> {
        self.edits.clear();
        let current = std::mem::take(&mut self.zippers);
        let mut next = Vec::new();
        let mut operations = current
            .into_iter()
            .rev()
            .map(|zipper| Operation::Up {
                node: zipper.focus,
                memo: zipper.memo,
            })
            .collect::<Vec<_>>();
        while let Some(operation) = operations.pop() {
            match operation {
                Operation::Down {
                    context,
                    expression,
                } => self.down(context, expression, &mut operations),
                Operation::DownFresh { memo, node } => {
                    self.down_fresh(memo, node, &token, &mut next, &mut operations)
                }
                Operation::Up { node, memo } => self.up(node, memo, &mut operations),
                Operation::UpContext {
                    expression,
                    context,
                } => self.up_context(expression, context, &mut operations),
            }
        }
        self.zippers = next;
        self.position = self
            .position
            .checked_add(1)
            .expect("input position space exhausted");
        Derivative {
            pwz: self,
            zippers: &self.zippers,
            edits: &self.edits,
        }
    }

    // d↓
    fn down(
        &mut self,
        context: ContextId,
        expression: ExpressionId,
        operations: &mut Vec<Operation<P>>,
    ) {
        let current_memo = self.expression(expression).memo;
        if let Some(memo) =
            current_memo.filter(|memo| self.memo(*memo).start == Some(self.position))
        {
            self.append_parent(memo, context);
            if self.memo(memo).end == Some(self.position) {
                let result = self
                    .memo(memo)
                    .result
                    .expect("a completed memo has a result expression");
                operations.push(Operation::UpContext {
                    expression: result,
                    context,
                });
            }
            return;
        }

        let memo = self.insert_memo(Some(self.position));
        self.append_parent(memo, context);
        self.set_expression_memo(expression, memo);
        let node = self.expression(expression).node.clone();
        operations.push(Operation::DownFresh { memo, node });
    }

    // d₀↓
    fn down_fresh(
        &mut self,
        memo: MemoId,
        node: ExpressionNode<P>,
        token: &Token<P>,
        output: &mut Vec<Zipper<P>>,
        operations: &mut Vec<Operation<P>>,
    ) {
        match node {
            ExpressionNode::Tok(expected) => {
                if token.terminal == expected {
                    output.push(Zipper {
                        focus: ExpressionNode::Seq {
                            symbol: Symbol::Token(token.clone()),
                            children: Vec::new(),
                        },
                        memo,
                    });
                }
            }
            ExpressionNode::Seq { symbol, children } => {
                let Some((&first, right)) = children.split_first() else {
                    operations.push(Operation::Up {
                        node: ExpressionNode::Seq {
                            symbol,
                            children: Vec::new(),
                        },
                        memo,
                    });
                    return;
                };

                let alternative = self.insert_context(Context::Alt { memo });
                let sequence_memo = self.insert_memo(self.memo(memo).start);
                self.append_parent(sequence_memo, alternative);
                let sequence = self.insert_context(Context::Seq {
                    memo: sequence_memo,
                    symbol,
                    left: Vec::new(),
                    right: right.to_vec(),
                });
                operations.push(Operation::Down {
                    context: sequence,
                    expression: first,
                });
            }
            ExpressionNode::Alt { children } => {
                let alternative = self.insert_context(Context::Alt { memo });
                for child in children.into_iter().rev() {
                    if self
                        .select
                        .get(&child)
                        .is_some_and(|terminals| terminals.binary_search(&token.terminal).is_err())
                    {
                        continue;
                    }
                    operations.push(Operation::Down {
                        context: alternative,
                        expression: child,
                    });
                }
            }
        }
    }

    // d↑
    fn up(&mut self, node: ExpressionNode<P>, memo: MemoId, operations: &mut Vec<Operation<P>>) {
        let expression = self.insert_expression(node);
        self.set_memo_result(memo, expression);
        let parents = self.memo(memo).parents.clone();
        for context in parents.into_iter().rev() {
            operations.push(Operation::UpContext {
                expression,
                context,
            });
        }
    }

    // d₀↑
    fn up_context(
        &mut self,
        expression: ExpressionId,
        context: ContextId,
        operations: &mut Vec<Operation<P>>,
    ) {
        match self.context(context).clone() {
            Context::Top => {}
            Context::Seq {
                memo,
                symbol,
                mut left,
                right,
            } => {
                let Some((&next, rest)) = right.split_first() else {
                    left.push(expression);
                    operations.push(Operation::Up {
                        node: ExpressionNode::Seq {
                            symbol,
                            children: left,
                        },
                        memo,
                    });
                    return;
                };

                left.push(expression);
                let next_context = self.insert_context(Context::Seq {
                    memo,
                    symbol,
                    left,
                    right: rest.to_vec(),
                });
                operations.push(Operation::Down {
                    context: next_context,
                    expression: next,
                });
            }
            Context::Alt { memo } => {
                if self.memo(memo).end == Some(self.position) {
                    let alternative = self
                        .memo(memo)
                        .result
                        .expect("a completed alternative memo has a result");
                    self.append_alternative_child(alternative, expression);
                } else {
                    operations.push(Operation::Up {
                        node: ExpressionNode::Alt {
                            children: vec![expression],
                        },
                        memo,
                    });
                }
            }
        }
    }

    fn insert_expression(&mut self, node: ExpressionNode<P>) -> ExpressionId {
        let id = ExpressionId(self.next_expression);
        self.next_expression = self
            .next_expression
            .checked_add(1)
            .expect("expression ID space exhausted");
        let value = Expression {
            memo: None,
            fixed: true,
            node,
        };
        assert!(self.expressions.insert(id, value).is_none());
        self.edits.push(Edit::NewExpression(id));
        id
    }

    fn insert_memo(&mut self, start: Option<usize>) -> MemoId {
        let id = MemoId(self.next_memo);
        self.next_memo = self
            .next_memo
            .checked_add(1)
            .expect("memo ID space exhausted");
        let value = Memo {
            start,
            parents: Vec::new(),
            end: None,
            result: None,
        };
        assert!(self.memos.insert(id, value).is_none());
        id
    }

    fn insert_context(&mut self, value: Context<P>) -> ContextId {
        let id = ContextId(self.next_context);
        self.next_context = self
            .next_context
            .checked_add(1)
            .expect("context ID space exhausted");
        assert!(self.contexts.insert(id, value).is_none());
        self.edits.push(Edit::NewContext(id));
        id
    }

    fn set_expression_memo(&mut self, expression: ExpressionId, memo: MemoId) {
        let value = self
            .expressions
            .get_mut(&expression)
            .expect("unknown expression ID");
        value.memo = Some(memo);
    }

    fn append_parent(&mut self, memo: MemoId, context: ContextId) {
        let value = self.memos.get_mut(&memo).expect("unknown memo ID");
        value.parents.push(context);
        self.edits.push(Edit::MemoParentAppended { memo, context });
    }

    fn set_memo_result(&mut self, memo: MemoId, result: ExpressionId) {
        let value = self.memos.get_mut(&memo).expect("unknown memo ID");
        value.end = Some(self.position);
        value.result = Some(result);
    }

    fn append_alternative_child(&mut self, alternative: ExpressionId, child: ExpressionId) {
        let ExpressionNode::Alt { children } = &mut self
            .expressions
            .get_mut(&alternative)
            .expect("unknown alternative expression")
            .node
        else {
            panic!("an alternative memo result must be an Alt expression");
        };
        children.push(child);
        self.edits
            .push(Edit::AlternativeChildAppended { alternative, child });
    }

    fn expression(&self, id: ExpressionId) -> &Expression<P> {
        self.expressions.get(&id).expect("unknown expression ID")
    }

    fn memo(&self, id: MemoId) -> &Memo {
        self.memos.get(&id).expect("unknown memo ID")
    }

    fn context(&self, id: ContextId) -> &Context<P> {
        self.contexts.get(&id).expect("unknown context ID")
    }
}

impl<P> ExpressionNode<P> {
    fn children(&self) -> &[ExpressionId] {
        match self {
            Self::Tok(_) => &[],
            Self::Seq { children, .. } | Self::Alt { children } => children,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ExpressionId as E, ExpressionNode, Grammar, Pwz, Symbol, Token};

    const A: u32 = 1;
    const B: u32 = 2;
    const C: u32 = 3;
    const D: u32 = 4;
    const S: u32 = 10;

    type Payload = &'static str;

    fn grammar(
        root: u32,
        nodes: impl IntoIterator<Item = (u32, ExpressionNode<Payload>)>,
    ) -> Grammar<Payload> {
        Grammar {
            root: E(root),
            expressions: nodes.into_iter().map(|(id, node)| (E(id), node)).collect(),
            select: Default::default(),
        }
    }

    fn tok(token: u32) -> ExpressionNode<Payload> {
        ExpressionNode::Tok(token)
    }

    fn seq(children: &[u32]) -> ExpressionNode<Payload> {
        ExpressionNode::Seq {
            symbol: Symbol::Grammar(S),
            children: children.iter().copied().map(E).collect(),
        }
    }

    fn alt(children: &[u32]) -> ExpressionNode<Payload> {
        ExpressionNode::Alt {
            children: children.iter().copied().map(E).collect(),
        }
    }

    fn input(terminal: u32, payload: Payload) -> Token<Payload> {
        Token { terminal, payload }
    }

    #[test]
    fn sequence_resumes_at_the_next_token() {
        let mut parser = Pwz::new(grammar(0, [(0, seq(&[1, 2])), (1, tok(A)), (2, tok(B))]));

        let first = parser.derive(input(A, "first-a"));
        assert_eq!(first.zippers.len(), 1);
        assert_eq!(
            &first.zippers[0].focus,
            &ExpressionNode::Seq {
                symbol: Symbol::Token(input(A, "first-a")),
                children: Vec::new(),
            }
        );
        let second = parser.derive(input(B, "second-b"));
        assert_eq!(second.zippers.len(), 1);
        assert!(parser.derive(input(C, "miss")).zippers.is_empty());
    }

    #[test]
    fn completed_sequence_preserves_three_child_source_order() {
        let mut parser = Pwz::new(grammar(
            0,
            [(0, seq(&[1, 2, 3])), (1, tok(A)), (2, tok(B)), (3, tok(C))],
        ));

        assert_eq!(parser.derive(input(A, "a")).zippers.len(), 1);
        assert_eq!(parser.derive(input(B, "b")).zippers.len(), 1);
        assert_eq!(parser.derive(input(C, "c")).zippers.len(), 1);
        parser.derive(input(D, "after"));
        let children = parser
            .expressions
            .values()
            .find_map(|expression| match &expression.node {
                ExpressionNode::Seq {
                    symbol: Symbol::Grammar(S),
                    children,
                } if children.len() == 3
                    && children.iter().all(|child| {
                        matches!(
                            parser.expressions[child].node,
                            ExpressionNode::Seq {
                                symbol: Symbol::Token(_),
                                ..
                            }
                        )
                    }) =>
                {
                    Some(children.clone())
                }
                _ => None,
            })
            .expect("the completed three-child sequence was not materialized");
        let payloads = children
            .iter()
            .map(|child| match &parser.expressions[child].node {
                ExpressionNode::Seq {
                    symbol: Symbol::Token(token),
                    children,
                } if children.is_empty() => token.payload,
                _ => panic!("sequence child is not a consumed token"),
            })
            .collect::<Vec<_>>();
        assert_eq!(payloads, ["a", "b", "c"]);
    }

    #[test]
    fn alternation_explores_each_child() {
        let source = grammar(0, [(0, alt(&[1, 2])), (1, tok(A)), (2, tok(B))]);
        let mut left = Pwz::new(source.clone());
        let mut right = Pwz::new(source.clone());
        let mut miss = Pwz::new(source);

        assert_eq!(left.derive(input(A, "left")).zippers.len(), 1);
        assert_eq!(right.derive(input(B, "right")).zippers.len(), 1);
        assert!(miss.derive(input(C, "miss")).zippers.is_empty());
    }

    #[test]
    fn shared_expression_reaches_both_continuations() {
        // (A B) | (A C), with the same Tok(A) node shared by both branches.
        let source = grammar(
            0,
            [
                (0, alt(&[1, 2])),
                (1, seq(&[3, 4])),
                (2, seq(&[3, 5])),
                (3, tok(A)),
                (4, tok(B)),
                (5, tok(C)),
            ],
        );
        let mut left = Pwz::new(source.clone());
        let mut right = Pwz::new(source);

        assert_eq!(left.derive(input(A, "shared-left")).zippers.len(), 1);
        assert_eq!(right.derive(input(A, "shared-right")).zippers.len(), 1);
        assert_eq!(left.derive(input(B, "left")).zippers.len(), 1);
        assert_eq!(right.derive(input(C, "right")).zippers.len(), 1);
    }

    #[test]
    fn left_recursion_streams_without_unfolding_the_cycle_eagerly() {
        // E ::= E A | B, accepting B A*.
        let mut parser = Pwz::new(grammar(
            0,
            [
                (0, alt(&[1, 2])),
                (1, seq(&[0, 3])),
                (2, tok(B)),
                (3, tok(A)),
            ],
        ));

        assert_eq!(parser.derive(input(B, "base")).zippers.len(), 1);
        assert_eq!(parser.derive(input(A, "suffix-1")).zippers.len(), 1);
        assert_eq!(parser.derive(input(A, "suffix-2")).zippers.len(), 1);
    }

    #[test]
    fn non_expanding_recursive_cycle_terminates() {
        // E ::= E epsilon | B. The recursive branch consumes no additional
        // token, matching the non-expanding cycle discussed in Section 7.
        let mut parser = Pwz::new(grammar(
            0,
            [
                (0, alt(&[1, 2])),
                (1, seq(&[0, 3])),
                (2, tok(B)),
                (3, seq(&[])),
            ],
        ));

        assert_eq!(parser.derive(input(B, "base")).zippers.len(), 1);
        assert!(parser.derive(input(A, "miss")).zippers.is_empty());
    }

    #[test]
    fn long_right_recursive_prefix_uses_the_operation_stack() {
        // E ::= A E | B. Completing B unwinds every pending right-recursive
        // context during the following derivative.
        let mut parser = Pwz::new(grammar(
            0,
            [
                (0, alt(&[1, 2])),
                (1, seq(&[3, 0])),
                (2, tok(B)),
                (3, tok(A)),
            ],
        ));

        for _ in 0..2_000 {
            assert_eq!(parser.derive(input(A, "prefix")).zippers.len(), 1);
        }
        assert_eq!(parser.derive(input(B, "base")).zippers.len(), 1);
        assert!(parser.derive(input(C, "after")).zippers.is_empty());
    }
}
