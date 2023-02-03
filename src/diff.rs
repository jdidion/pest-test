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
                                ))
                            }
                            Some(actual_child) if expected_names.contains(actual_child.name()) => {
                                children.push(ExpressionDiff::Missing(expected_child.clone()));
                                while let Some(next) = expected_iter.peek() {
                                    if next.name() == actual_child.name() {
                                        break;
                                    } else {
                                        children.push(ExpressionDiff::Missing(
                                            expected_iter.next().unwrap().clone(),
                                        ));
                                    }
                                }
                            }
                            Some(actual_child) => {
                                children.push(ExpressionDiff::Extra(actual_child.clone()))
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
