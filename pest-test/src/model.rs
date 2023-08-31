use crate::parser::Rule;
use colored::{Color, Colorize};
use pest::{iterators::Pair, RuleType};
use snailquote::unescape;
use std::{
    collections::HashSet,
    fmt::{Display, Result as FmtResult, Write},
};
use thiserror::Error;

#[derive(Error, Debug)]
#[error("Error creating model element from parser pair")]
pub struct ModelError(String);

impl ModelError {
    fn from_str(msg: &str) -> Self {
        Self(msg.to_owned())
    }
}

fn assert_rule<'a>(pair: Pair<'a, Rule>, rule: Rule) -> Result<Pair<'a, Rule>, ModelError> {
    if pair.as_rule() == rule {
        Ok(pair)
    } else {
        Err(ModelError(format!(
            "Expected pair {:?} rule to be {:?}",
            pair, rule
        )))
    }
}

#[derive(Clone, Debug)]
pub enum Expression {
    Terminal {
        name: String,
        value: Option<String>,
    },
    NonTerminal {
        name: String,
        children: Vec<Expression>,
    },
    Skip {
        depth: usize,
        next: Box<Expression>,
    },
}

impl Expression {
    pub fn try_from_sexpr<'a>(pair: Pair<'a, Rule>) -> Result<Self, ModelError> {
        let mut inner = pair.into_inner();
        let skip_depth: usize = if inner.peek().map(|pair| pair.as_rule()) == Some(Rule::skip) {
            let depth_pair = inner
                .next()
                .unwrap()
                .into_inner()
                .next()
                .ok_or_else(|| ModelError::from_str("Missing skip depth"))
                .and_then(|pair| assert_rule(pair, Rule::int))?;
            depth_pair
                .as_str()
                .parse()
                .map_err(|err| ModelError(format!("Error parsing skip depth: {:?}", err)))?
        } else {
            0
        };
        let name = inner
            .next()
            .ok_or_else(|| ModelError::from_str("Missing rule name"))
            .and_then(|pair| assert_rule(pair, Rule::identifier))
            .map(|pair| pair.as_str().to_owned())?;
        let expr = match inner.next() {
            None => Self::Terminal { name, value: None },
            Some(pair) => match pair.as_rule() {
                Rule::sub_expressions => {
                    let children: Result<Vec<Expression>, ModelError> = pair
                        .into_inner()
                        .map(|pair| Self::try_from_sexpr(pair))
                        .collect();
                    Self::NonTerminal {
                        name,
                        children: children?,
                    }
                }
                Rule::string => {
                    let s = pair.as_str().trim();
                    let value = Some(unescape(s).map_err(|err| {
                        ModelError(format!("Error unescaping string value {}: {:?}", s, err))
                    })?);
                    Self::Terminal { name, value }
                }
                other => return Err(ModelError(format!("Unexpected rule {:?}", other))),
            },
        };
        if skip_depth == 0 {
            Ok(expr)
        } else {
            Ok(Self::Skip {
                depth: skip_depth,
                next: Box::new(expr),
            })
        }
    }

    pub fn try_from_code<'a, R: RuleType>(
        pair: Pair<'a, R>,
        skip_rules: &HashSet<R>,
    ) -> Result<Self, ModelError> {
        let name = format!("{:?}", pair.as_rule());
        let value = pair.as_str();
        let children: Result<Vec<Expression>, ModelError> = pair
            .into_inner()
            .filter(|pair| !skip_rules.contains(&pair.as_rule()))
            .map(|pair| Self::try_from_code(pair, skip_rules))
            .collect();
        match children {
            Ok(children) if children.is_empty() => Ok(Self::Terminal {
                name,
                value: Some(value.to_owned()),
            }),
            Ok(children) => Ok(Self::NonTerminal {
                name,
                children: children,
            }),
            Err(e) => Err(e),
        }
    }

    pub fn name(&self) -> &String {
        match self {
            Self::Terminal { name, value: _ } => name,
            Self::NonTerminal { name, children: _ } => name,
            Self::Skip { depth: _, next } => next.name(),
        }
    }

    pub fn skip_depth(&self) -> usize {
        match self {
            Expression::Skip { depth, next: _ } => *depth,
            _ => 0,
        }
    }

    /// Returns the `Nth` descendant of this expression, where `N = depth`. For a
    /// `NonTerminal` expression, the descendant is its first child. For a `Terminal` node, there
    /// is no descendant.
    pub fn get_descendant(&self, depth: usize) -> Option<&Expression> {
        if depth > 0 {
            match self {
                Self::NonTerminal { name: _, children } if !children.is_empty() => {
                    children.first().unwrap().get_descendant(depth - 1)
                }
                Self::Skip {
                    depth: skip_depth,
                    next,
                } if *skip_depth <= depth => next.as_ref().get_descendant(depth - skip_depth),
                _ => None,
            }
        } else {
            Some(self)
        }
    }
}

pub struct ExpressionFormatter<'a> {
    writer: &'a mut dyn Write,
    indent: &'a str,
    pub(crate) level: usize,
    pub(crate) color: Option<Color>,
    buffering: bool,
}

impl<'a> ExpressionFormatter<'a> {
    pub fn from_defaults(writer: &'a mut dyn Write) -> Self {
        Self {
            writer,
            indent: "  ",
            level: 0,
            color: None,
            buffering: true,
        }
    }

    pub(crate) fn write_indent(&mut self) -> FmtResult {
        for _ in 0..self.level {
            self.writer.write_str(self.indent)?;
        }
        Ok(())
    }

    pub(crate) fn write_newline(&mut self) -> FmtResult {
        self.writer.write_char('\n')
    }

    pub(crate) fn write_char(&mut self, c: char) -> FmtResult {
        match self.color {
            Some(color) => self
                .writer
                .write_str(format!("{}", c.to_string().color(color)).as_ref()),
            None => self.writer.write_char(c),
        }
    }

    pub(crate) fn write_str(&mut self, s: &str) -> FmtResult {
        match self.color {
            Some(color) => self
                .writer
                .write_str(format!("{}", s.color(color)).as_ref()),
            None => self.writer.write_str(s),
        }
    }

    fn fmt_buffered(&mut self, expression: &Expression) -> FmtResult {
        let mut buf = String::with_capacity(1024);
        let mut string_formatter = ExpressionFormatter {
            writer: &mut buf,
            indent: self.indent,
            level: self.level,
            color: None,
            buffering: false,
        };
        string_formatter.fmt(expression)?;
        self.write_str(buf.as_ref())?;
        Ok(())
    }

    fn fmt_unbuffered(&mut self, expression: &Expression) -> FmtResult {
        self.write_indent()?;
        match expression {
            Expression::Terminal { name, value } => {
                self.write_char('(')?;
                self.write_str(name)?;
                if let Some(value) = value {
                    self.write_str(": \"")?;
                    self.write_str(value)?;
                    self.write_char('"')?;
                }
                self.write_char(')')?;
            }
            Expression::NonTerminal { name, children } if children.is_empty() => {
                self.write_char('(')?;
                self.write_str(name)?;
                self.write_char(')')?;
            }
            Expression::NonTerminal { name, children } => {
                self.write_char('(')?;
                self.write_str(name)?;
                self.write_newline()?;
                self.level += 1;
                for child in children {
                    self.fmt(child)?;
                    self.write_newline()?;
                }
                self.level -= 1;
                self.write_indent()?;
                self.write_char(')')?;
            }
            Expression::Skip { depth, next } => {
                self.write_str(format!("#[skip(depth = {})]", depth).as_ref())?;
                self.write_newline()?;
                self.fmt_unbuffered(next.as_ref())?;
            }
        }
        Ok(())
    }

    pub fn fmt(&mut self, expression: &Expression) -> FmtResult {
        if self.buffering {
            self.fmt_buffered(expression)
        } else {
            self.fmt_unbuffered(expression)
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        ExpressionFormatter::from_defaults(f).fmt(self)
    }
}

#[derive(Clone, Debug)]
pub struct TestCase {
    pub name: String,
    pub code: String,
    pub expression: Expression,
}

impl TestCase {
    pub fn try_from_pair<'a>(pair: Pair<'a, Rule>) -> Result<Self, ModelError> {
        let mut inner = pair.into_inner();
        let name = inner
            .next()
            .ok_or_else(|| ModelError::from_str("Missing test name"))
            .and_then(|pair| assert_rule(pair, Rule::test_name))
            .map(|pair| pair.as_str().trim().to_owned())?;
        let mut code_block = inner
            .next()
            .ok_or_else(|| ModelError::from_str("Missing code block"))
            .and_then(|pair| assert_rule(pair, Rule::code_block))
            .map(|pair| pair.into_inner())?;
        let div = code_block
            .next()
            .ok_or_else(|| ModelError::from_str("Missing div"))
            .and_then(|pair| assert_rule(pair, Rule::div))
            .map(|pair| pair.as_str())?;
        let mut code = code_block
            .next()
            .ok_or_else(|| ModelError::from_str("Missing code"))
            .and_then(|pair| assert_rule(pair, Rule::code))
            .map(|pair| pair.as_str())?;
        let expression = inner
            .next()
            .ok_or_else(|| ModelError::from_str("Missing expression"))
            .and_then(|pair| assert_rule(pair, Rule::expression))?;
        if !div.starts_with('+'){
            code = code.trim();
        }
        Ok(TestCase {
            name,
            code: code.to_owned(),
            expression: Expression::try_from_sexpr(expression)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Expression, ExpressionFormatter, TestCase};
    use crate::{
        parser::{Rule, TestParser},
        TestError,
    };
    use indoc::indoc;
    use std::collections::HashSet;

    fn assert_nonterminal<'a>(
        expression: &'a Expression,
        expected_name: &str,
    ) -> &'a Vec<Expression> {
        match expression {
            Expression::NonTerminal { name, children } => {
                assert_eq!(name, expected_name);
                children
            }
            _ => panic!("Expected non-terminal expression but found {expression:?}"),
        }
    }

    fn assert_skip<'a>(expression: &'a Expression, expected_depth: usize) -> &'a Box<Expression> {
        match expression {
            Expression::Skip { depth, next } => {
                assert_eq!(expected_depth, *depth);
                next
            }
            _ => panic!("Expected skip expression but found {expression:?}"),
        }
    }

    fn assert_terminal(expression: &Expression, expected_name: &str, expected_value: Option<&str>) {
        match expression {
            Expression::Terminal { name, value } => {
                assert_eq!(name, expected_name);
                match (value, expected_value) {
                    (Some(actual), Some(expected)) => assert_eq!(actual.trim(), expected),
                    (Some(actual), None) => {
                        panic!("Terminal node has value {actual} but there is no expected value")
                    }
                    (None, Some(expected)) => {
                        panic!("Terminal node has no value but expected {expected}")
                    }
                    _ => (),
                }
            }
            _ => panic!("Expected terminal expression but found {expression:?}"),
        }
    }

    fn assert_nonterminal_sexpr<'a>(
        expression: &'a Expression,
        expected_name: &str,
    ) -> &'a Vec<Expression> {
        let children = assert_nonterminal(expression, "expression");
        assert_eq!(children.len(), 2);
        assert_terminal(&children[0], "identifier", Some(expected_name));
        assert_nonterminal(&children[1], "sub_expressions")
    }

    fn assert_terminal_sexpr(
        expression: &Expression,
        expected_name: &str,
        expected_value: Option<&str>,
    ) {
        let children = assert_nonterminal(expression, "expression");
        assert!(children.len() >= 1);
        assert_terminal(&children[0], "identifier", Some(expected_name));
        if expected_value.is_some() {
            assert_eq!(children.len(), 2);
            let value = assert_nonterminal(&children[1], "string");
            assert_eq!(value.len(), 1);
            assert_terminal(&value[0], "string_value", expected_value);
        }
    }

    const WITH_QUOTE: &str = indoc! {r#"
    Quoted
    ======

    x = "hi"
    
    ======

    (source_file
        (declaration
            (identifier: "x")
            (value: "\"hi\"")
        )
    )
    "#};

    #[test]
    fn test_quoted_value() -> Result<(), TestError<Rule>> {
        let test_case: TestCase = TestParser::parse(WITH_QUOTE)
            .map_err(|source| TestError::Parser { source })
            .and_then(|pair| {
                TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })
            })?;
        let expression = test_case.expression;
        let children = assert_nonterminal(&expression, "source_file");
        assert_eq!(children.len(), 1);
        let children = assert_nonterminal(&children[0], "declaration");
        assert_eq!(children.len(), 2);
        assert_terminal(&children[0], "identifier", Some("x"));
        assert_terminal(&children[1], "value", Some("\"hi\""));
        Ok(())
    }

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

    #[test]
    fn test_parse_from_code() -> Result<(), TestError<Rule>> {
        let test_pair = TestParser::parse(TEXT).map_err(|source| TestError::Parser { source })?;
        let skip_rules = HashSet::from([Rule::EOI]);
        let code_expression = Expression::try_from_code(test_pair, &skip_rules)
            .map_err(|source| TestError::Model { source })?;
        let children = assert_nonterminal(&code_expression, "test_case");
        assert_eq!(children.len(), 3);
        assert_terminal(&children[0], "test_name", Some("My Test"));
        let code_block = assert_nonterminal(&children[1], "code_block");
        assert_eq!(code_block.len(), 2);
        assert_terminal(&code_block[0], "div", Some("======="));
        assert_terminal(&code_block[1], "code", Some("fn x() int {\n  return 1;\n}"));
        let s_expression = assert_nonterminal_sexpr(&children[2], "source_file");
        assert_eq!(s_expression.len(), 1);
        let s_expression = assert_nonterminal_sexpr(&s_expression[0], "function_definition");
        assert_eq!(s_expression.len(), 4);
        assert_terminal_sexpr(&s_expression[0], "identifier", Some("x"));
        assert_terminal_sexpr(&s_expression[1], "parameter_list", None);
        assert_terminal_sexpr(&s_expression[2], "primitive_type", Some("int"));
        let s_expression = assert_nonterminal_sexpr(&s_expression[3], "block");
        assert_eq!(s_expression.len(), 1);
        let s_expression = assert_nonterminal_sexpr(&s_expression[0], "return_statement");
        assert_eq!(s_expression.len(), 1);
        assert_terminal_sexpr(&s_expression[0], "number", Some("1"));
        Ok(())
    }

    const TEXT_WITH_SKIP: &str = indoc! {r#"
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
          #[skip(depth = 1)]
          (return_statement 
            (number: "1")
          )
        )
      )
    )
    "#};

    #[test]
    fn test_parse() -> Result<(), TestError<Rule>> {
        let test_case: TestCase = TestParser::parse(TEXT_WITH_SKIP)
            .map_err(|source| TestError::Parser { source })
            .and_then(|pair| {
                TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })
            })?;
        assert_eq!(test_case.name, "My Test");
        assert_eq!(test_case.code, "fn x() int {\n  return 1;\n}");
        let expression = test_case.expression;
        let children = assert_nonterminal(&expression, "source_file");
        assert_eq!(children.len(), 1);
        let children = assert_nonterminal(&children[0], "function_definition");
        assert_eq!(children.len(), 4);
        assert_terminal(&children[0], "identifier", Some("x"));
        assert_terminal(&children[1], "parameter_list", None);
        assert_terminal(&children[2], "primitive_type", Some("int"));
        let children = assert_nonterminal(&children[3], "block");
        assert_eq!(children.len(), 1);
        let next = assert_skip(&children[0], 1);
        let children = assert_nonterminal(&next, "return_statement");
        assert_eq!(children.len(), 1);
        assert_terminal(&children[0], "number", Some("1"));
        Ok(())
    }

    #[test]
    fn test_format() -> Result<(), TestError<Rule>> {
        let mut writer = String::new();
        let mut formatter = ExpressionFormatter::from_defaults(&mut writer);
        let test_case: TestCase = TestParser::parse(TEXT_WITH_SKIP)
            .map_err(|source| TestError::Parser { source })
            .and_then(|pair| {
                TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })
            })?;
        formatter
            .fmt(&test_case.expression)
            .expect("Error formatting expression");
        let expected = indoc! {r#"
        (source_file
          (function_definition
            (identifier: "x")
            (parameter_list)
            (primitive_type: "int")
            (block
              #[skip(depth = 1)]
              (return_statement
                (number: "1")
              )
            )
          )
        )"#};
        assert_eq!(writer, expected);
        Ok(())
    }
}
