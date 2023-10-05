pub mod diff;
pub mod model;
mod parser;

use crate::{
    diff::ExpressionDiff,
    model::{Expression, ModelError, TestCase},
    parser::{ParserError, Rule, TestParser},
};
use pest::{error::Error as PestError, Parser, RuleType};
use std::{
    collections::HashSet, fs::read_to_string, io::Error as IOError, marker::PhantomData,
    path::PathBuf,
};
use thiserror::Error;

pub fn cargo_manifest_dir() -> PathBuf {
    PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap().as_str())
}

pub fn default_test_dir() -> PathBuf {
    cargo_manifest_dir().join("tests").join("pest")
}

#[derive(Error, Debug)]
pub enum TestError<R> {
    #[error("Error reading test case from file")]
    IO { source: IOError },
    #[error("Error parsing test case")]
    Parser { source: ParserError<Rule> },
    #[error("Error building model from test case parse tree")]
    Model { source: ModelError },
    #[error("Error parsing code with target parser")]
    Target { source: Box<PestError<R>> },
    #[error("Expected and actual parse trees are different:\n{diff}")]
    Diff { diff: ExpressionDiff },
}

pub struct PestTester<R: RuleType, P: Parser<R>> {
    test_dir: PathBuf,
    test_ext: String,
    rule: R,
    skip_rules: HashSet<R>,
    parser: PhantomData<P>,
}

impl<R: RuleType, P: Parser<R>> PestTester<R, P> {
    /// Creates a new `PestTester` that looks for tests in `test_dir` and having file extension
    /// `test_ext`. Code is parsed beinning at `rule` and the rules in `skip_rule` are ignored
    /// when comparing to the expected expression.
    pub fn new<D: Into<PathBuf>, S: AsRef<str>>(
        test_dir: D,
        test_ext: S,
        rule: R,
        skip_rules: HashSet<R>,
    ) -> Self {
        Self {
            test_dir: test_dir.into(),
            test_ext: test_ext.as_ref().to_owned(),
            rule,
            skip_rules,
            parser: PhantomData::<P>,
        }
    }

    /// Creates a new `PestTester` that looks for tests in `<crate root>/tests/pest` and having
    /// file extension ".txt". Code is parsed beinning at `rule` and the rules in `skip_rule` are
    /// ignored when comparing to the expected expression.
    pub fn from_defaults(rule: R, skip_rules: HashSet<R>) -> Self {
        Self::new(default_test_dir(), ".txt", rule, skip_rules)
    }

    /// Evaluates the test with the given name. If `ignore_missing_expected_values` is true, then
    /// the test is not required to specify values for non-terminal nodes.
    pub fn evaluate<N: AsRef<str>>(
        &self,
        name: N,
        ignore_missing_expected_values: bool,
    ) -> Result<(), TestError<R>> {
        let path = self
            .test_dir
            .join(format!("{}.{}", name.as_ref(), self.test_ext));
        let text = read_to_string(path).map_err(|source| TestError::IO { source })?;
        let pair =
            TestParser::parse(text.as_ref()).map_err(|source| TestError::Parser { source })?;
        let test_case =
            TestCase::try_from_pair(pair).map_err(|source| TestError::Model { source })?;
        let code_pair =
            parser::parse(test_case.code.as_ref(), self.rule, self.parser).map_err(|source| {
                match source {
                    ParserError::Empty => TestError::Parser {
                        source: ParserError::Empty,
                    },
                    ParserError::Pest { source } => TestError::Target { source },
                }
            })?;
        let code_expr = Expression::try_from_code(code_pair, &self.skip_rules)
            .map_err(|source| TestError::Model { source })?;
        match ExpressionDiff::from_expressions(
            &test_case.expression,
            &code_expr,
            ignore_missing_expected_values,
        ) {
            ExpressionDiff::Equal(_) => Ok(()),
            diff => Err(TestError::Diff { diff }),
        }
    }

    /// Equivalent to `self.evaluate(name, true)
    pub fn evaluate_strict<N: AsRef<str>>(&self, name: N) -> Result<(), TestError<R>> {
        self.evaluate(name, false)
    }
}
