/// Abstract syntax trees: constructor applications over number and text leaves.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ast {
    Constructor { name: String, children: Vec<Ast> },
    Number(i64),
    Text(String),
}

impl Ast {
    /// Builds a constructor node.
    pub fn constructor(name: &str, children: Vec<Ast>) -> Ast {
        Ast::Constructor {
            name: name.to_string(),
            children,
        }
    }

    /// Renders this tree as an egglog expression, without recursion.
    pub fn to_egglog(&self) -> String {
        enum Task<'a> {
            Node(&'a Ast),
            Text(&'static str),
        }
        let mut rendered = String::new();
        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => rendered.push_str(text),
                Task::Node(Ast::Number(value)) => rendered.push_str(&value.to_string()),
                Task::Node(Ast::Text(value)) => {
                    rendered.push('"');
                    for character in value.chars() {
                        match character {
                            '"' => rendered.push_str("\\\""),
                            '\\' => rendered.push_str("\\\\"),
                            other => rendered.push(other),
                        }
                    }
                    rendered.push('"');
                }
                Task::Node(Ast::Constructor { name, children }) => {
                    rendered.push('(');
                    rendered.push_str(name);
                    tasks.push(Task::Text(")"));
                    for child in children.iter().rev() {
                        tasks.push(Task::Node(child));
                        tasks.push(Task::Text(" "));
                    }
                }
            }
        }
        rendered
    }
}

#[cfg(test)]
mod tests {
    use super::Ast;

    #[test]
    fn renders_numbers_and_negatives() {
        assert_eq!(Ast::Number(7).to_egglog(), "7");
        assert_eq!(Ast::Number(-7).to_egglog(), "-7");
    }

    #[test]
    fn renders_text_with_escapes() {
        assert_eq!(Ast::Text("a\"b\\c".into()).to_egglog(), "\"a\\\"b\\\\c\"");
    }

    #[test]
    fn renders_nested_constructors() {
        let tree = Ast::constructor(
            "Add",
            vec![
                Ast::constructor("Num", vec![Ast::Number(1)]),
                Ast::constructor("Num", vec![Ast::Number(2)]),
            ],
        );
        assert_eq!(tree.to_egglog(), "(Add (Num 1) (Num 2))");
    }
}
