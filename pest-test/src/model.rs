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

fn assert_rule(pair: Pair<'_, Rule>, rule: Rule) -> Result<Pair<'_, Rule>, ModelError> {
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
    pub fn try_from_sexpr(pair: Pair<'_, Rule>) -> Result<Self, ModelError> {
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
                    let children: Result<Vec<Expression>, ModelError> =
                        pair.into_inner().map(Self::try_from_sexpr).collect();
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

    pub fn try_from_code<R: RuleType>(
        pair: Pair<'_, R>,
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
            Ok(children) => Ok(Self::NonTerminal { name, children }),
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
                    self.write_str(&value.escape_default().to_string())?;
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
    pub fn try_from_pair(pair: Pair<'_, Rule>) -> Result<Self, ModelError> {
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
        code_block
            .next()
            .ok_or_else(|| ModelError::from_str("Missing div"))
            .and_then(|pair| assert_rule(pair, Rule::div))?;
        let code_untrimmed = code_block
            .next()
            .ok_or_else(|| ModelError::from_str("Missing code"))
            .and_then(|pair| assert_rule(pair, Rule::code))
            .map(|pair| pair.as_str())?;
        // The code must start and end with at least one line separator - remove first and last
        let code_len = code_untrimmed.len();
        assert!(code_len >= 2);
        let mut code_chars = code_untrimmed.chars();
        let code_start: usize = match code_chars.next() {
            Some('\n') => 1,
            Some('\r') => match code_chars.next() {
                Some('\n') if code_len > 2 => 2,
                _ => 1,
            },
            _ => {
                return Err(ModelError::from_str(
                    "Code block must be preceeded by at least one line separator",
                ))
            }
        };
        let mut code_chars = code_untrimmed.chars().rev();
        let code_end: usize = code_len
            - match code_chars.next() {
                Some('\r') => 1,
                Some('\n') => match code_chars.next() {
                    Some('\r') if code_len - code_start > 2 => 2,
                    _ => 1,
                },
                _ => {
                    return Err(ModelError::from_str(
                        "Code block must be followed by at least one line separator",
                    ))
                }
            };
        let code = code_untrimmed[code_start..code_end].to_owned();
        let expression = inner
            .next()
            .ok_or_else(|| ModelError::from_str("Missing expression"))
            .and_then(|pair| assert_rule(pair, Rule::expression))?;
        Ok(TestCase {
            name,
            code,
            expression: Expression::try_from_sexpr(expression)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{assert_rule, Expression, ExpressionFormatter, ModelError, TestCase};
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

    fn assert_skip(expression: &Expression, expected_depth: usize) -> &Expression {
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
        assert!(!children.is_empty());
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

    const BLANK_LINES: &str = indoc! {r#"


"#};

    #[test]
    fn test_escape_whitespace() -> Result<(), TestError<Rule>> {
        let mut writer = String::new();
        let mut formatter = ExpressionFormatter::from_defaults(&mut writer);
        let expression = Expression::Terminal {
            name: "blank_lines".to_string(),
            value: Some(BLANK_LINES.to_string()),
        };
        formatter
            .fmt(&expression)
            .expect("Error formatting expression");
        let expected = r#"(blank_lines: "\n\n")"#;
        assert_eq!(writer, expected);
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
        assert_eq!(test_case.code, "\nfn x() int {\n  return 1;\n}\n");
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
        let children = assert_nonterminal(next, "return_statement");
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

    /// `assert_rule` should pass the pair through unchanged when the rule
    /// matches and return a descriptive `ModelError` when it does not. The
    /// error branch (and `ModelError`'s `Display`) is otherwise only hit on
    /// malformed input, so exercise it directly.
    #[test]
    fn test_assert_rule() {
        // Parse a known test case and grab its top-level pair, which is a
        // `Rule::test_case`.
        let pair = TestParser::parse(TEXT).expect("parse failed");
        // Matching rule: returns Ok with the same pair.
        let ok = assert_rule(pair.clone(), Rule::test_case);
        assert!(ok.is_ok());
        // Mismatched rule: returns Err whose Display is the model-error message.
        let err = assert_rule(pair, Rule::identifier).unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("Error creating model element"),
            "unexpected ModelError display: {msg}"
        );
    }

    #[test]
    fn test_model_error_debug() {
        // The `#[error(...)]` Display and derived Debug should both render.
        let err = ModelError::from_str("boom");
        assert_eq!(
            format!("{err}"),
            "Error creating model element from parser pair"
        );
        assert!(format!("{err:?}").contains("boom"));
    }

    /// `get_descendant(0)` returns the node itself; descending into a terminal
    /// yields `None`; descending through a `Skip` consumes its depth.
    #[test]
    fn test_get_descendant() {
        let terminal = Expression::Terminal {
            name: "leaf".to_owned(),
            value: None,
        };
        // depth 0 => the node itself.
        assert!(matches!(
            terminal.get_descendant(0),
            Some(Expression::Terminal { .. })
        ));
        // A terminal has no children, so any positive depth is None.
        assert!(terminal.get_descendant(1).is_none());

        let nested = Expression::NonTerminal {
            name: "outer".to_owned(),
            children: vec![Expression::NonTerminal {
                name: "inner".to_owned(),
                children: vec![Expression::Terminal {
                    name: "leaf".to_owned(),
                    value: Some("v".to_owned()),
                }],
            }],
        };
        assert_eq!(nested.get_descendant(2).unwrap().name(), "leaf");
        // Descending past the bottom yields None.
        assert!(nested.get_descendant(3).is_none());

        // A Skip with depth == requested descent forwards to `next`.
        let skip = Expression::Skip {
            depth: 1,
            next: Box::new(Expression::Terminal {
                name: "skipped".to_owned(),
                value: None,
            }),
        };
        assert_eq!(skip.get_descendant(1).unwrap().name(), "skipped");
        // Requesting a descent shallower than the skip depth yields None.
        let deep_skip = Expression::Skip {
            depth: 3,
            next: Box::new(Expression::Terminal {
                name: "skipped".to_owned(),
                value: None,
            }),
        };
        assert!(deep_skip.get_descendant(1).is_none());
        // `name()` on a Skip delegates to its `next`.
        assert_eq!(skip.name(), "skipped");
        // `skip_depth()` reports the depth for Skip and 0 otherwise.
        assert_eq!(skip.skip_depth(), 1);
        assert_eq!(terminal.skip_depth(), 0);
    }

    /// A string value with an invalid escape sequence should surface as a
    /// `ModelError` from `try_from_sexpr` (the `unescape` error branch).
    #[test]
    fn test_try_from_sexpr_unescape_error() {
        // The grammar's `string_value` rule accepts any non-quote character,
        // including a backslash followed by `z`. That sequence is not a valid
        // escape, so `snailquote::unescape` fails and we get a ModelError.
        const BAD_ESCAPE: &str = "Bad\n=====\n\nx\n\n=====\n\n(node: \"\\z\")\n";
        let pair = TestParser::parse(BAD_ESCAPE).expect("parse should succeed");
        let result = TestCase::try_from_pair(pair);
        match result {
            Err(err) => assert!(format!("{err:?}").contains("unescaping")),
            Ok(tc) => panic!("expected unescape error, got {tc:?}"),
        }
    }

    /// CRLF line endings around the code block must be trimmed correctly,
    /// exercising the `\r\n` arms of the code-trimming logic.
    #[test]
    fn test_crlf_code_trimming() -> Result<(), TestError<Rule>> {
        // Build the test text with explicit CRLF separators around the code.
        let text = "My Test\r\n=======\r\nfn x() int {}\r\n=======\r\n(node)\r\n";
        let test_case: TestCase = TestParser::parse(text)
            .map_err(|source| TestError::Parser { source })
            .and_then(|pair| {
                TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })
            })?;
        // The outermost CRLF separators are trimmed; the code itself remains.
        assert_eq!(test_case.code, "fn x() int {}");
        Ok(())
    }

    /// Bare carriage-return (old-Mac) line endings around the code block hit
    /// the `\r`-not-followed-by-`\n` arm at the start and the bare-`\r` arm at
    /// the end of the code-trimming logic.
    #[test]
    fn test_bare_cr_code_trimming() -> Result<(), TestError<Rule>> {
        let text = "My Test\r=======\rfn x() int {}\r=======\r(node)\r";
        let test_case: TestCase = TestParser::parse(text)
            .map_err(|source| TestError::Parser { source })
            .and_then(|pair| {
                TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })
            })?;
        assert_eq!(test_case.code, "fn x() int {}");
        Ok(())
    }
}
