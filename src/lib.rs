pub mod diff;
pub mod model;
mod parser;

use crate::{
    diff::{diff_expressions, ExpressionDiff},
    model::{Expression, ModelError, TestCase},
    parser::{ParserError, Rule, TestParser},
};
use pest::{error::Error as PestError, Parser, RuleType};
use std::{fs::read_to_string, io::Error as IOError, marker::PhantomData, path::PathBuf};

#[derive(Debug)]
pub enum Error<R> {
    IO { source: IOError },
    Parser { source: ParserError<Rule> },
    Model { source: ModelError },
    Target { source: PestError<R> },
    Diff { diff: ExpressionDiff },
}

pub struct PestTester<R: RuleType, P: Parser<R>> {
    test_dir: PathBuf,
    test_ext: String,
    rule: R,
    parser: PhantomData<P>,
}

impl<R: RuleType, P: Parser<R>> PestTester<R, P> {
    pub fn new<D: Into<PathBuf>, S: AsRef<str>>(test_dir: D, test_ext: S, rule: R) -> Self {
        Self {
            test_dir: test_dir.into(),
            test_ext: test_ext.as_ref().to_owned(),
            rule,
            parser: PhantomData::<P>,
        }
    }

    pub fn from_defaults(rule: R) -> Self {
        let default_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("parser");
        let default_ext = ".txt";
        Self::new(default_dir, default_ext, rule)
    }

    pub fn evaluate<N: AsRef<str>>(
        &self,
        name: N,
        ignore_missing_expected_values: bool,
    ) -> Result<(), Error<R>> {
        let path = self
            .test_dir
            .join(format!("{}.{}", name.as_ref(), self.test_ext));
        let text = read_to_string(path).map_err(|source| Error::IO { source })?;
        let pair = TestParser::parse(text.as_ref()).map_err(|source| Error::Parser { source })?;
        let test_case = TestCase::try_from_pair(pair).map_err(|source| Error::Model { source })?;
        let code_pair =
            parser::parse(test_case.code.as_ref(), self.rule, self.parser).map_err(|source| {
                match source {
                    ParserError::Empty => Error::Parser {
                        source: ParserError::Empty,
                    },
                    ParserError::Pest { source } => Error::Target { source },
                }
            })?;
        let code_expr =
            Expression::try_from_code(code_pair).map_err(|source| Error::Model { source })?;
        match diff_expressions(
            &test_case.expression,
            &code_expr,
            ignore_missing_expected_values,
        ) {
            ExpressionDiff::Equal(_) => Ok(()),
            diff => Err(Error::Diff { diff }),
        }
    }

    pub fn evaluate_strict<N: AsRef<str>>(&self, name: N) -> Result<(), Error<R>> {
        self.evaluate(name, false)
    }
}
