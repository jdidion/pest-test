use crate::model::{Expression, ExpressionFormatter};
use colored::Color;
use std::{
    collections::HashSet,
    fmt::{Display, Result as FmtResult},
};

#[derive(Debug)]
pub enum ExpressionDiff {
    Equal(Expression),
    NotEqual {
        expected: Expression,
        actual: Expression,
    },
    Missing(Expression),
    Extra(Expression),
    Parital {
        name: String,
        children: Vec<ExpressionDiff>,
    },
}

impl ExpressionDiff {
    pub fn from_expressions(
        expected: &Expression,
        actual: &Expression,
        ignore_missing_expected_values: bool,
    ) -> ExpressionDiff {
        match (expected, actual) {
            (
                Expression::Terminal {
                    name: expected_name,
                    value: expected_value,
                },
                Expression::Terminal {
                    name: actual_name,
                    value: actual_value,
                },
            ) if expected_name == actual_name && expected_value == actual_value => {
                ExpressionDiff::Equal(expected.clone())
            }
            (
                Expression::Terminal {
                    name: expected_name,
                    value: expected_value,
                },
                Expression::Terminal {
                    name: actual_name,
                    value: _,
                },
            ) if expected_name == actual_name
                && expected_value.is_none()
                && ignore_missing_expected_values =>
            {
                ExpressionDiff::Equal(actual.clone())
            }
            (
                Expression::NonTerminal {
                    name: expected_name,
                    children: expected_children,
                },
                Expression::NonTerminal {
                    name: actual_name,
                    children: actual_children,
                },
            ) if expected_name == actual_name => {
                let expected_names: HashSet<&String> =
                    expected_children.iter().map(|expr| expr.name()).collect();
                let mut expected_iter = expected_children.iter().peekable();
                let mut actual_iter = actual_children.iter();
                let mut children = Vec::new();
                loop {
                    if let Some(expected_child) = expected_iter.next() {
                        match actual_iter.next() {
                            Some(actual_child) if expected_child.name() == actual_child.name() => {
                                children.push(Self::from_expressions(
                                    expected_child,
                                    actual_child,
                                    ignore_missing_expected_values,
                                ));
                            }
                            Some(actual_child) => {
                                children.push(ExpressionDiff::Missing(expected_child.clone()));
                                if expected_names.contains(actual_child.name()) {
                                    while let Some(next) = expected_iter.peek() {
                                        if next.name() == actual_child.name() {
                                            break;
                                        } else {
                                            children.push(ExpressionDiff::Missing(
                                                expected_iter.next().unwrap().clone(),
                                            ));
                                        }
                                    }
                                } else {
                                    children.push(ExpressionDiff::Extra(actual_child.clone()))
                                }
                            }
                            None => children.push(ExpressionDiff::Missing(expected_child.clone())),
                        }
                    } else {
                        children.extend(
                            actual_iter
                                .map(|actual_child| ExpressionDiff::Extra(actual_child.clone())),
                        );
                        break;
                    }
                }
                let partial = children
                    .iter()
                    .filter(|child| match child {
                        ExpressionDiff::Equal(_) => false,
                        _ => true,
                    })
                    .count()
                    > 0;
                if partial {
                    ExpressionDiff::Parital {
                        name: expected_name.clone(),
                        children,
                    }
                } else {
                    ExpressionDiff::Equal(Expression::NonTerminal {
                        name: expected_name.clone(),
                        children: children
                            .into_iter()
                            .map(|child| match child {
                                ExpressionDiff::Equal(expression) => expression,
                                _ => panic!("Unexpected non-equal value"),
                            })
                            .collect(),
                    })
                }
            }
            _ => ExpressionDiff::NotEqual {
                expected: expected.clone(),
                actual: actual.clone(),
            },
        }
    }

    pub fn name(&self) -> String {
        match self {
            ExpressionDiff::Equal(exp) => exp.name().clone(),
            ExpressionDiff::NotEqual { expected, actual } if expected.name() == actual.name() => {
                expected.name().to_owned()
            }
            ExpressionDiff::NotEqual { expected, actual } => {
                format!("{}/{}", expected.name(), actual.name())
            }
            ExpressionDiff::Missing(exp) => exp.name().to_owned(),
            ExpressionDiff::Extra(exp) => exp.name().to_owned(),
            ExpressionDiff::Parital { name, children: _ } => name.to_owned(),
        }
    }
}

trait DiffExt {
    fn fmt_diff(
        &mut self,
        diff: &ExpressionDiff,
        expected_color: Option<Color>,
        actual_color: Option<Color>,
    ) -> FmtResult;
}

impl<'a> DiffExt for ExpressionFormatter<'a> {
    fn fmt_diff(
        &mut self,
        diff: &ExpressionDiff,
        expected_color: Option<Color>,
        actual_color: Option<Color>,
    ) -> FmtResult {
        match diff {
            ExpressionDiff::Equal(expression) => self.fmt(expression)?,
            ExpressionDiff::NotEqual { expected, actual } => {
                self.color = expected_color;
                self.fmt(expected)?;
                self.write_newline()?;
                self.color = actual_color;
                self.fmt(actual)?;
                self.color = None;
            }
            ExpressionDiff::Missing(expression) => {
                self.color = expected_color;
                self.fmt(expression)?;
                self.color = None;
            }
            ExpressionDiff::Extra(expression) => {
                self.color = actual_color;
                self.fmt(expression)?;
                self.color = None;
            }
            ExpressionDiff::Parital { name, children } => {
                self.write_indent()?;
                self.write_char('(')?;
                self.write_str(name)?;
                self.write_newline()?;
                self.level += 1;
                for child in children {
                    self.fmt_diff(child, expected_color, actual_color)?;
                    self.write_newline()?;
                }
                self.level -= 1;
                self.write_indent()?;
                self.write_char(')')?;
            }
        }
        Ok(())
    }
}

impl Display for ExpressionDiff {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        ExpressionFormatter::from_defaults(f).fmt_diff(self, Some(Color::Green), Some(Color::Red))
    }
}

#[cfg(test)]
mod tests {
    use super::ExpressionDiff;
    use crate::{
        model::{Expression, TestCase},
        parser::Rule,
        TestError, TestParser,
    };
    use indoc::indoc;

    const TEXT: &str = indoc! {r#"
    My Test

    =======

    fn x() int {
      return 1;
    }

    =======
    
    (source_file
      (function_definition
        (identifier: "x")
        (parameter_list)
        (primitive_type: "int")
        (block
          (return_statement 
            (number: "1")
          )
        )
      )
    )
    "#};

    fn assert_partial<'a>(
        diff: &'a ExpressionDiff,
        expected_name: &'a str,
    ) -> &'a Vec<ExpressionDiff> {
        match diff {
            ExpressionDiff::Parital { name, children } => {
                assert_eq!(expected_name, name);
                children
            }
            _ => panic!("Expected diff to be partial but was {}", diff),
        }
    }

    fn assert_value_equal(
        diff: &ExpressionDiff,
        expected_name: &str,
        expected_value: Option<&str>,
    ) {
        match diff {
            ExpressionDiff::Equal(Expression::Terminal { name, value }) => {
                assert_eq!(expected_name, name);
                match (expected_value, value) {
                    (Some(expected), Some(actual)) => assert_eq!(expected, actual),
                    _ => (),
                }
            }
            _ => panic!("Expectedc diff to be equal but was {}", diff),
        }
    }

    fn assert_value_nonequal(
        diff: &ExpressionDiff,
        name: &str,
        expected_expected_value: Option<&str>,
        expected_actual_value: Option<&str>,
    ) {
        match diff {
            ExpressionDiff::NotEqual {
                expected:
                    Expression::Terminal {
                        name: expected_name,
                        value: expected_value,
                    },
                actual:
                    Expression::Terminal {
                        name: actual_name,
                        value: actual_value,
                    },
            } => {
                assert_eq!(expected_name, name);
                assert_eq!(actual_name, name);
                assert_eq!(
                    expected_expected_value.map(|s| s.to_owned()),
                    *expected_value
                );
                assert_eq!(expected_actual_value.map(|s| s.to_owned()), *actual_value);
            }
            _ => panic!("Expected diff to be non-equal but was {}", diff),
        }
    }

    fn assert_missing(diff: &ExpressionDiff, expected_name: &str) {
        match diff {
            ExpressionDiff::Missing(expr) => assert_eq!(expr.name(), expected_name),
            _ => panic!("Expected diff to be missing but was {}", diff),
        }
    }

    fn assert_extra(diff: &ExpressionDiff, expected_name: &str) {
        match diff {
            ExpressionDiff::Extra(expr) => assert_eq!(expr.name(), expected_name),
            _ => panic!("Expected diff to be extra but was {}", diff),
        }
    }

    fn assert_nonequal_type(diff: &ExpressionDiff, expected_name: &str) {
        match diff {
            ExpressionDiff::NotEqual {
                expected:
                    Expression::Terminal {
                        name: terminal_name,
                        value: _,
                    },
                actual:
                    Expression::NonTerminal {
                        name: nonterminal_name,
                        children: _,
                    },
            } => {
                assert_eq!(expected_name, nonterminal_name);
                assert_eq!(expected_name, terminal_name);
            }
            ExpressionDiff::NotEqual {
                expected:
                    Expression::NonTerminal {
                        name: nonterminal_name,
                        children: _,
                    },
                actual:
                    Expression::Terminal {
                        name: terminal_name,
                        value: _,
                    },
            } => {
                assert_eq!(expected_name, nonterminal_name);
                assert_eq!(expected_name, terminal_name);
            }
            _ => panic!("Expected diff to be non-equal but was {}", diff),
        }
    }

    #[test]
    fn test_diff() -> Result<(), TestError<Rule>> {
        let test_case: TestCase = TestParser::parse(TEXT)
            .map_err(|source| TestError::Parser { source })
            .and_then(|pair| {
                TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })
            })?;
        let expected_sexpr = Expression::NonTerminal {
            name: String::from("source_file"),
            children: Vec::from([Expression::NonTerminal {
                name: String::from("function_definition"),
                children: Vec::from([
                    Expression::Terminal {
                        name: String::from("identifier"),
                        value: Some(String::from("y")),
                    },
                    Expression::NonTerminal {
                        name: String::from("missing"),
                        children: Vec::from([Expression::Terminal {
                            name: String::from("foo"),
                            value: None,
                        }]),
                    },
                    Expression::Terminal {
                        name: String::from("primitive_type"),
                        value: None,
                    },
                    Expression::NonTerminal {
                        name: String::from("block"),
                        children: Vec::from([Expression::Terminal {
                            name: String::from("return_statement"),
                            value: None,
                        }]),
                    },
                ]),
            }]),
        };
        let diff_strict =
            ExpressionDiff::from_expressions(&expected_sexpr, &test_case.expression, false);
        let children = assert_partial(&diff_strict, "source_file");
        assert_eq!(children.len(), 1);
        let children = assert_partial(&children[0], "function_definition");
        assert_eq!(children.len(), 5);
        assert_value_nonequal(&children[0], "identifier", Some("y"), Some("x"));
        assert_missing(&children[1], "missing");
        assert_extra(&children[2], "parameter_list");
        assert_value_nonequal(&children[3], "primitive_type", None, Some("int"));
        let children = assert_partial(&children[4], "block");
        assert_eq!(children.len(), 1);
        assert_nonequal_type(&children[0], "return_statement");

        let diff_lenient =
            ExpressionDiff::from_expressions(&expected_sexpr, &test_case.expression, true);
        let children = assert_partial(&diff_lenient, "source_file");
        let children = assert_partial(&children[0], "function_definition");
        assert_value_equal(&children[3], "primitive_type", Some("int"));
        Ok(())
    }

    // fn test_format() -> Result<(), TestError<Rule>> {
    //     Ok(())
    // }
}
