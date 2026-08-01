use std::collections::{BTreeMap, BTreeSet};

use egglog::ast::{Action, Command, Expr, Fact, GenericActions, GenericRule, Parser, Subdatatypes};
use egglog::prelude::{RustSpan, Span};
use thiserror::Error;

const FREE_COMMAND: &str = "free";
const PRIMITIVE_SORTS: &[&str] = &["Unit", "String", "bool", "i64", "f64", "BigInt", "BigRat"];

/// The generated disjointness theory for one equality sort.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FreeSortSpec {
    pub(crate) sort: String,
    pub(crate) relation: String,
    /// Private unary relation which marks the classes where demand-driven
    /// free-constructor reasoning should run for this sort.
    pub(crate) reach: String,
    pub(crate) constructors: Vec<String>,
    /// True when every constructor field is primitive or belongs to another
    /// complete free sort. In that case the generated structural rules cover
    /// the whole mutually-recursive family rooted at this sort.
    pub(crate) complete: bool,
}

/// An egglog program with every `(free Sort Relation)` marker replaced by
/// ordinary declarations and rules.
#[derive(Clone, Debug)]
pub(crate) struct FreeProgramExpansion {
    pub(crate) commands: Vec<Command>,
    #[allow(dead_code)]
    pub(crate) source: String,
    pub(crate) free_sorts: Vec<FreeSortSpec>,
}

#[derive(Debug, Error)]
pub(crate) enum FreeExpansionError {
    #[error("could not parse egglog program while expanding `free`: {0}")]
    Parse(#[from] egglog::ast::ParseError),
    #[error("invalid private free-constructor ruleset name `{0}`")]
    InvalidRuleset(String),
    #[error("malformed free declaration; expected `(free Sort Relation)`")]
    MalformedFree,
    #[error("free sort and relation names must be ordinary, non-global egglog atoms")]
    InvalidFreeName,
    #[error("sort `{0}` is not a declared equality sort")]
    UnknownFreeSort(String),
    #[error("sort `{0}` has more than one free declaration")]
    DuplicateFreeSort(String),
    #[error("disjoint relation `{0}` is assigned to more than one free sort")]
    DuplicateFreeRelation(String),
    #[error("generated disjoint relation `{0}` collides with an existing egglog function")]
    RelationCollision(String),
    #[error("generated free-focus relation `{0}` collides with an existing egglog function")]
    ReachCollision(String),
    #[error("constructor `{0}` is declared more than once")]
    DuplicateConstructor(String),
    #[error("`{0}` is already a combined ruleset and cannot receive generated rules")]
    CombinedRulesetCollision(String),
}

#[derive(Clone, Debug)]
struct ConstructorDecl {
    name: String,
    inputs: Vec<String>,
    output: String,
}

#[derive(Clone, Debug)]
struct FreeDecl {
    sort: String,
    relation: String,
}

/// Parse and expand the source-level `(free Sort Relation)` extension.
///
/// The returned commands can be passed directly to `EGraph::run_program`.
/// The rendered source is equivalent and is useful to clients which retain a
/// source-oriented initialization path.
#[allow(dead_code)]
pub(crate) fn expand_free_program(
    source: &str,
    private_ruleset: &str,
) -> Result<FreeProgramExpansion, FreeExpansionError> {
    let commands = Parser::default().get_program_from_string(None, source)?;
    expand_free_commands(commands, private_ruleset)
}

/// Expand already-parsed commands. Unknown egglog commands and all ordinary
/// commands are preserved in their original order; generated declarations and
/// rules are appended, after all user declarations are available for
/// typechecking.
pub(crate) fn expand_free_commands(
    commands: Vec<Command>,
    private_ruleset: &str,
) -> Result<FreeProgramExpansion, FreeExpansionError> {
    if !ordinary_atom(private_ruleset) {
        return Err(FreeExpansionError::InvalidRuleset(
            private_ruleset.to_owned(),
        ));
    }

    let mut equality_sorts = BTreeSet::new();
    let mut constructors = BTreeMap::<String, ConstructorDecl>::new();
    let mut occupied_functions = BTreeSet::new();
    let mut existing_ruleset = false;
    let mut combined_ruleset = false;

    for command in &commands {
        match command {
            Command::Sort(_, name, None) => {
                equality_sorts.insert(name.clone());
            }
            Command::Datatype { name, variants, .. } => {
                equality_sorts.insert(name.clone());
                for variant in variants {
                    insert_constructor(
                        &mut constructors,
                        &mut occupied_functions,
                        ConstructorDecl {
                            name: variant.name.clone(),
                            inputs: variant.types.clone(),
                            output: name.clone(),
                        },
                    )?;
                }
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, name, definition) in datatypes {
                    if let Subdatatypes::Variants(variants) = definition {
                        equality_sorts.insert(name.clone());
                        for variant in variants {
                            insert_constructor(
                                &mut constructors,
                                &mut occupied_functions,
                                ConstructorDecl {
                                    name: variant.name.clone(),
                                    inputs: variant.types.clone(),
                                    output: name.clone(),
                                },
                            )?;
                        }
                    }
                }
            }
            Command::Constructor { name, schema, .. } => {
                insert_constructor(
                    &mut constructors,
                    &mut occupied_functions,
                    ConstructorDecl {
                        name: name.clone(),
                        inputs: schema.input.clone(),
                        output: schema.output.clone(),
                    },
                )?;
            }
            Command::Function { name, .. } | Command::Relation { name, .. } => {
                occupied_functions.insert(name.clone());
            }
            Command::AddRuleset(_, name) if name == private_ruleset => {
                existing_ruleset = true;
            }
            Command::UnstableCombinedRuleset(_, name, _) if name == private_ruleset => {
                combined_ruleset = true;
            }
            _ => {}
        }
    }
    if combined_ruleset {
        return Err(FreeExpansionError::CombinedRulesetCollision(
            private_ruleset.to_owned(),
        ));
    }

    let mut retained = Vec::with_capacity(commands.len());
    let mut free_by_sort = BTreeMap::<String, FreeDecl>::new();
    let mut used_relations = BTreeSet::new();
    for command in commands {
        match parse_free_declaration(&command)? {
            Some(declaration) => {
                if !equality_sorts.contains(&declaration.sort) {
                    return Err(FreeExpansionError::UnknownFreeSort(declaration.sort));
                }
                if occupied_functions.contains(&declaration.relation) {
                    return Err(FreeExpansionError::RelationCollision(declaration.relation));
                }
                if free_by_sort.contains_key(&declaration.sort) {
                    return Err(FreeExpansionError::DuplicateFreeSort(declaration.sort));
                }
                if !used_relations.insert(declaration.relation.clone()) {
                    return Err(FreeExpansionError::DuplicateFreeRelation(
                        declaration.relation,
                    ));
                }
                free_by_sort.insert(declaration.sort.clone(), declaration);
            }
            None => retained.push(command),
        }
    }

    if free_by_sort.is_empty() {
        let source = render_commands(&retained);
        return Ok(FreeProgramExpansion {
            commands: retained,
            source,
            free_sorts: Vec::new(),
        });
    }

    let reach_by_sort = free_by_sort
        .keys()
        .enumerate()
        .map(|(index, sort)| {
            (
                sort.clone(),
                format!("{private_ruleset}_free_reach_{index}"),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for reach in reach_by_sort.values() {
        if occupied_functions.contains(reach) || used_relations.contains(reach) {
            return Err(FreeExpansionError::ReachCollision(reach.clone()));
        }
    }

    if !existing_ruleset {
        retained.push(Command::AddRuleset(
            egglog::span!(),
            private_ruleset.to_owned(),
        ));
    }
    for declaration in free_by_sort.values() {
        retained.push(Command::Relation {
            span: egglog::span!(),
            name: declaration.relation.clone(),
            inputs: vec![declaration.sort.clone(), declaration.sort.clone()],
        });
        retained.push(Command::Relation {
            span: egglog::span!(),
            name: reach_by_sort[&declaration.sort].clone(),
            inputs: vec![declaration.sort.clone()],
        });
    }

    let constructors_by_sort = constructors_by_output(&constructors);
    let complete_sorts = complete_free_sorts(&free_by_sort, &constructors_by_sort, &equality_sorts);
    let mut free_sorts = Vec::with_capacity(free_by_sort.len());
    for declaration in free_by_sort.values() {
        let sort_constructors = constructors_by_sort
            .get(&declaration.sort)
            .cloned()
            .unwrap_or_default();
        append_free_rules(
            &mut retained,
            declaration,
            &sort_constructors,
            &free_by_sort,
            &reach_by_sort,
            &equality_sorts,
            private_ruleset,
        );
        free_sorts.push(FreeSortSpec {
            sort: declaration.sort.clone(),
            relation: declaration.relation.clone(),
            reach: reach_by_sort[&declaration.sort].clone(),
            constructors: sort_constructors
                .iter()
                .map(|constructor| constructor.name.clone())
                .collect(),
            complete: complete_sorts.contains(&declaration.sort),
        });
    }

    let source = render_commands(&retained);
    Ok(FreeProgramExpansion {
        commands: retained,
        source,
        free_sorts,
    })
}

fn insert_constructor(
    constructors: &mut BTreeMap<String, ConstructorDecl>,
    occupied_functions: &mut BTreeSet<String>,
    constructor: ConstructorDecl,
) -> Result<(), FreeExpansionError> {
    if constructors.contains_key(&constructor.name) {
        return Err(FreeExpansionError::DuplicateConstructor(constructor.name));
    }
    occupied_functions.insert(constructor.name.clone());
    constructors.insert(constructor.name.clone(), constructor);
    Ok(())
}

fn parse_free_declaration(command: &Command) -> Result<Option<FreeDecl>, FreeExpansionError> {
    let Command::Action(Action::Expr(_, Expr::Call(_, function, arguments))) = command else {
        return Ok(None);
    };
    if function != FREE_COMMAND {
        return Ok(None);
    }
    let [sort, relation] = arguments.as_slice() else {
        return Err(FreeExpansionError::MalformedFree);
    };
    let (Expr::Var(_, sort), Expr::Var(_, relation)) = (sort, relation) else {
        return Err(FreeExpansionError::MalformedFree);
    };
    if !ordinary_atom(sort) || !ordinary_atom(relation) {
        return Err(FreeExpansionError::InvalidFreeName);
    }
    Ok(Some(FreeDecl {
        sort: sort.clone(),
        relation: relation.clone(),
    }))
}

fn ordinary_atom(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with('$')
        && !name.chars().any(|character| {
            character.is_whitespace() || matches!(character, '(' | ')' | '"' | ';')
        })
}

fn constructors_by_output(
    constructors: &BTreeMap<String, ConstructorDecl>,
) -> BTreeMap<String, Vec<ConstructorDecl>> {
    let mut by_output = BTreeMap::<String, Vec<ConstructorDecl>>::new();
    for constructor in constructors.values() {
        by_output
            .entry(constructor.output.clone())
            .or_default()
            .push(constructor.clone());
    }
    by_output
}

/// Greatest fixed point: recursive and mutually-recursive free families are
/// complete, while a path to an opaque/container/non-free field makes every
/// referring sort incomplete.
fn complete_free_sorts(
    free_by_sort: &BTreeMap<String, FreeDecl>,
    constructors_by_sort: &BTreeMap<String, Vec<ConstructorDecl>>,
    equality_sorts: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut complete = free_by_sort.keys().cloned().collect::<BTreeSet<_>>();
    loop {
        let incomplete = complete
            .iter()
            .filter(|sort| {
                constructors_by_sort
                    .get(*sort)
                    .into_iter()
                    .flatten()
                    .flat_map(|constructor| &constructor.inputs)
                    .any(|input| {
                        !is_primitive(input)
                            && (!equality_sorts.contains(input) || !complete.contains(input))
                    })
            })
            .cloned()
            .collect::<Vec<_>>();
        if incomplete.is_empty() {
            return complete;
        }
        for sort in incomplete {
            complete.remove(&sort);
        }
    }
}

fn append_free_rules(
    commands: &mut Vec<Command>,
    declaration: &FreeDecl,
    constructors: &[ConstructorDecl],
    free_by_sort: &BTreeMap<String, FreeDecl>,
    reach_by_sort: &BTreeMap<String, String>,
    equality_sorts: &BTreeSet<String>,
    ruleset: &str,
) {
    let relation = &declaration.relation;
    let reach = &reach_by_sort[&declaration.sort];
    let left = variable("free_left");
    let right = variable("free_right");
    commands.push(rule(
        format!("{relation}:symmetry"),
        ruleset,
        vec![relation_fact(relation, left.clone(), right.clone())],
        vec![relation_action(relation, right.clone(), left.clone())],
    ));
    commands.push(rule(
        format!("{relation}:irreflexive"),
        ruleset,
        vec![relation_fact(relation, left.clone(), left)],
        vec![Action::Panic(
            egglog::span!(),
            format!(
                "free sort `{}` became disjoint from itself",
                declaration.sort
            ),
        )],
    ));

    for (left_index, left_constructor) in constructors.iter().enumerate() {
        for right_constructor in &constructors[left_index + 1..] {
            commands.push(no_confusion_rule(
                relation,
                reach,
                left_constructor,
                right_constructor,
                ruleset,
            ));
        }
        append_same_constructor_rules(
            commands,
            relation,
            reach,
            left_constructor,
            free_by_sort,
            equality_sorts,
            ruleset,
        );
        append_reach_projection_rule(
            commands,
            relation,
            reach,
            left_constructor,
            reach_by_sort,
            ruleset,
        );
    }
}

fn no_confusion_rule(
    relation: &str,
    reach: &str,
    left_constructor: &ConstructorDecl,
    right_constructor: &ConstructorDecl,
    ruleset: &str,
) -> Command {
    let left_output = variable("free_left_output");
    let right_output = variable("free_right_output");
    let left_arguments = arguments("free_left_argument", left_constructor.inputs.len());
    let right_arguments = arguments("free_right_argument", right_constructor.inputs.len());
    rule(
        format!(
            "{relation}:no-confusion:{}:{}",
            left_constructor.name, right_constructor.name
        ),
        ruleset,
        vec![
            reach_fact(reach, left_output.clone()),
            reach_fact(reach, right_output.clone()),
            Fact::Eq(
                egglog::span!(),
                left_output.clone(),
                call(&left_constructor.name, left_arguments),
            ),
            Fact::Eq(
                egglog::span!(),
                right_output.clone(),
                call(&right_constructor.name, right_arguments),
            ),
        ],
        vec![relation_action(relation, left_output, right_output)],
    )
}

fn append_same_constructor_rules(
    commands: &mut Vec<Command>,
    output_relation: &str,
    output_reach: &str,
    constructor: &ConstructorDecl,
    free_by_sort: &BTreeMap<String, FreeDecl>,
    equality_sorts: &BTreeSet<String>,
    ruleset: &str,
) {
    let left_arguments = arguments("free_left_argument", constructor.inputs.len());
    let right_arguments = arguments("free_right_argument", constructor.inputs.len());
    let left_output = variable("free_left_output");
    let right_output = variable("free_right_output");

    let injective_actions = constructor
        .inputs
        .iter()
        .enumerate()
        .filter(|(_, sort)| equality_sorts.contains(*sort))
        .map(|(index, _)| {
            Action::Union(
                egglog::span!(),
                left_arguments[index].clone(),
                right_arguments[index].clone(),
            )
        })
        .collect::<Vec<_>>();
    if !injective_actions.is_empty() {
        commands.push(rule(
            format!("{output_relation}:injective:{}", constructor.name),
            ruleset,
            vec![
                reach_fact(output_reach, left_output.clone()),
                reach_fact(output_reach, right_output.clone()),
                Fact::Eq(
                    egglog::span!(),
                    left_output.clone(),
                    call(&constructor.name, left_arguments.clone()),
                ),
                Fact::Eq(
                    egglog::span!(),
                    right_output.clone(),
                    call(&constructor.name, right_arguments.clone()),
                ),
                Fact::Eq(egglog::span!(), left_output.clone(), right_output.clone()),
            ],
            injective_actions,
        ));
    }

    for (index, input_sort) in constructor.inputs.iter().enumerate() {
        let premise = if let Some(input) = free_by_sort.get(input_sort) {
            relation_fact(
                &input.relation,
                left_arguments[index].clone(),
                right_arguments[index].clone(),
            )
        } else if is_primitive(input_sort) {
            Fact::Fact(call(
                "!=",
                vec![
                    left_arguments[index].clone(),
                    right_arguments[index].clone(),
                ],
            ))
        } else {
            continue;
        };
        commands.push(rule(
            format!("{output_relation}:propagate:{}:{index}", constructor.name),
            ruleset,
            vec![
                reach_fact(output_reach, left_output.clone()),
                reach_fact(output_reach, right_output.clone()),
                Fact::Eq(
                    egglog::span!(),
                    left_output.clone(),
                    call(&constructor.name, left_arguments.clone()),
                ),
                Fact::Eq(
                    egglog::span!(),
                    right_output.clone(),
                    call(&constructor.name, right_arguments.clone()),
                ),
                premise,
            ],
            vec![relation_action(
                output_relation,
                left_output.clone(),
                right_output.clone(),
            )],
        ));
    }
}

fn append_reach_projection_rule(
    commands: &mut Vec<Command>,
    output_relation: &str,
    output_reach: &str,
    constructor: &ConstructorDecl,
    reach_by_sort: &BTreeMap<String, String>,
    ruleset: &str,
) {
    let constructor_arguments = arguments("free_reach_argument", constructor.inputs.len());
    let actions = constructor
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(index, sort)| {
            reach_by_sort.get(sort).map(|reach| {
                Action::Expr(
                    egglog::span!(),
                    call(reach, vec![constructor_arguments[index].clone()]),
                )
            })
        })
        .collect::<Vec<_>>();
    if actions.is_empty() {
        return;
    }
    let output = variable("free_reach_output");
    commands.push(rule(
        format!("{output_relation}:reach:{}", constructor.name),
        ruleset,
        vec![
            reach_fact(output_reach, output.clone()),
            Fact::Eq(
                egglog::span!(),
                output,
                call(&constructor.name, constructor_arguments),
            ),
        ],
        actions,
    ));
}

fn is_primitive(sort: &str) -> bool {
    PRIMITIVE_SORTS.contains(&sort)
}

fn variable(name: &str) -> Expr {
    Expr::Var(egglog::span!(), name.to_owned())
}

fn arguments(prefix: &str, arity: usize) -> Vec<Expr> {
    (0..arity)
        .map(|index| variable(&format!("{prefix}_{index}")))
        .collect()
}

fn call(function: &str, arguments: Vec<Expr>) -> Expr {
    Expr::Call(egglog::span!(), function.to_owned(), arguments)
}

fn relation_fact(relation: &str, left: Expr, right: Expr) -> Fact {
    Fact::Fact(call(relation, vec![left, right]))
}

fn reach_fact(reach: &str, value: Expr) -> Fact {
    Fact::Fact(call(reach, vec![value]))
}

fn relation_action(relation: &str, left: Expr, right: Expr) -> Action {
    Action::Expr(egglog::span!(), call(relation, vec![left, right]))
}

fn rule(name: String, ruleset: &str, body: Vec<Fact>, head: Vec<Action>) -> Command {
    Command::Rule {
        rule: GenericRule {
            span: egglog::span!(),
            head: GenericActions(head),
            body,
            name,
            ruleset: ruleset.to_owned(),
        },
    }
}

fn render_commands(commands: &[Command]) -> String {
    let mut source = commands
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    if !source.is_empty() {
        source.push('\n');
    }
    source
}

#[cfg(test)]
mod tests {
    use egglog::EGraph;

    use super::{FreeExpansionError, expand_free_program};

    const FREE_TYPES: &str = r#"
        (datatype Type)
        (constructor TArr (Type Type) Type)
        (constructor TInt () Type)
        (constructor TString () Type)
        (constructor Name (String) Type)
        (free Type Type-Disjoint)
    "#;

    fn saturated(
        program: &str,
        suffix: impl FnOnce(&[super::FreeSortSpec]) -> String,
    ) -> Result<EGraph, String> {
        let expansion =
            expand_free_program(program, "test-free-rules").map_err(|error| error.to_string())?;
        let suffix = suffix(&expansion.free_sorts);
        let mut egraph = EGraph::default();
        egraph
            .run_program(expansion.commands)
            .map_err(|error| error.to_string())?;
        egraph
            .parse_and_run_program(None, &suffix)
            .map_err(|error| error.to_string())?;
        Ok(egraph)
    }

    #[test]
    fn expands_marker_and_reports_complete_recursive_sort() {
        let expansion = expand_free_program(FREE_TYPES, "test-free-rules").unwrap();
        assert!(!expansion.source.contains("(free "));
        assert!(
            expansion
                .source
                .contains("(relation Type-Disjoint (Type Type))")
        );
        assert_eq!(expansion.free_sorts.len(), 1);
        let spec = &expansion.free_sorts[0];
        assert_eq!(spec.sort, "Type");
        assert_eq!(spec.relation, "Type-Disjoint");
        assert_eq!(spec.reach, "test-free-rules_free_reach_0");
        assert!(
            expansion
                .source
                .contains("(relation test-free-rules_free_reach_0 (Type))")
        );
        assert!(spec.complete);
        assert_eq!(spec.constructors, ["Name", "TArr", "TInt", "TString"]);
    }

    #[test]
    fn no_confusion_recursive_propagation_and_primitive_inequality_run_in_egglog() {
        saturated(FREE_TYPES, |specs| {
            format!(
                r#"
            (let $int (TInt))
            (let $string (TString))
            (let $left-arrow (TArr (TInt) (TInt)))
            (let $right-arrow (TArr (TInt) (TString)))
            (let $left-name (Name "left"))
            (let $right-name (Name "right"))
            ({reach} $left-arrow)
            ({reach} $right-arrow)
            ({reach} $left-name)
            ({reach} $right-name)
            (run test-free-rules 12)
            (check (Type-Disjoint $int $string))
            (check (Type-Disjoint $right-arrow $left-arrow))
            (check (Type-Disjoint $left-name $right-name))
            "#,
                reach = specs[0].reach
            )
        })
        .unwrap();
    }

    #[test]
    fn equality_of_free_nodes_unions_equality_sorted_fields() {
        assert!(
            saturated(FREE_TYPES, |specs| format!(
                r#"
            (let $int (TInt))
            (let $string (TString))
            (let $left-arrow (TArr $int $int))
            (let $right-arrow (TArr $string $string))
            ({reach} $left-arrow)
            ({reach} $right-arrow)
            (union $left-arrow $right-arrow)
            (run test-free-rules 4)
            (check (= $int $string))
            "#,
                reach = specs[0].reach
            ),)
            .is_err()
        );
        // The generated injectivity rule does merge the fields. The overall
        // run then correctly fails because no-confusion makes that merge a
        // reflexive Disjoint fact and the irreflexivity rule panics.
    }

    #[test]
    fn only_reached_terms_participate_in_disjointness_rules() {
        let expansion = expand_free_program(
            r#"
            (datatype Value)
            (constructor A (i64) Value)
            (constructor B (i64) Value)
            (free Value Value-Disjoint)
            "#,
            "test-free-rules",
        )
        .unwrap();
        let reach = expansion.free_sorts[0].reach.clone();
        let mut egraph = EGraph::default();
        egraph.run_program(expansion.commands).unwrap();

        let mut terms = String::new();
        for index in 0..128 {
            terms.push_str(&format!(
                "(let $a{index} (A {index}))\n(let $b{index} (B {index}))\n"
            ));
        }
        terms.push_str("(run test-free-rules 8)\n");
        egraph.parse_and_run_program(None, &terms).unwrap();
        assert_eq!(egraph.get_size("Value-Disjoint"), 0);

        egraph
            .parse_and_run_program(
                None,
                &format!(
                    r#"
                    ({reach} $a0)
                    ({reach} $b0)
                    (run test-free-rules 8)
                    (check (Value-Disjoint $a0 $b0))
                    "#
                ),
            )
            .unwrap();
        // The requested fact plus its symmetric counterpart, not the
        // 128-by-128 cross product of all constructor terms.
        assert_eq!(egraph.get_size("Value-Disjoint"), 2);
    }

    #[test]
    fn opaque_equality_field_marks_the_sort_incomplete() {
        let expansion = expand_free_program(
            r#"
            (datatype Ident)
            (datatype Type)
            (constructor TVar (Ident) Type)
            (free Type Type-Disjoint)
            "#,
            "test-free-rules",
        )
        .unwrap();
        assert!(!expansion.free_sorts[0].complete);
    }

    #[test]
    fn mutually_recursive_free_sorts_are_complete() {
        let expansion = expand_free_program(
            r#"
            (datatype Left)
            (datatype Right)
            (constructor ToRight (Right) Left)
            (constructor ToLeft (Left) Right)
            (free Left Left-Disjoint)
            (free Right Right-Disjoint)
            "#,
            "test-free-rules",
        )
        .unwrap();
        assert!(expansion.free_sorts.iter().all(|spec| spec.complete));
    }

    #[test]
    fn malformed_or_colliding_declarations_are_typed_errors() {
        assert!(matches!(
            expand_free_program("(datatype Type) (free Type)", "rules"),
            Err(FreeExpansionError::MalformedFree)
        ));
        assert!(matches!(
            expand_free_program(
                "(datatype Type) (relation D (Type Type)) (free Type D)",
                "rules"
            ),
            Err(FreeExpansionError::RelationCollision(name)) if name == "D"
        ));
        assert!(matches!(
            expand_free_program("(free Missing D)", "rules"),
            Err(FreeExpansionError::UnknownFreeSort(name)) if name == "Missing"
        ));
        assert!(matches!(
            expand_free_program(
                "(datatype Type) (relation rules_free_reach_0 (Type)) (free Type D)",
                "rules"
            ),
            Err(FreeExpansionError::ReachCollision(name)) if name == "rules_free_reach_0"
        ));
    }

    #[test]
    fn programs_without_free_markers_are_unchanged_except_for_formatting() {
        let expansion = expand_free_program("(datatype Type)\n", "rules").unwrap();
        assert!(expansion.free_sorts.is_empty());
        assert_eq!(expansion.commands.len(), 1);
        assert!(!expansion.source.contains("Type-Disjoint"));
    }
}
