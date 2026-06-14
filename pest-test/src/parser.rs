use pest::{error::Error as PestError, iterators::Pair, Parser, RuleType};
use std::marker::PhantomData;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParserError<R> {
    #[error("Error parsing source text")]
    Pest { source: Box<PestError<R>> },
    #[error("Empty parse tree")]
    Empty,
}

pub fn parse<R: RuleType, P: Parser<R>>(
    text: &str,
    rule: R,
    _: PhantomData<P>,
) -> Result<Pair<'_, R>, ParserError<R>> {
    P::parse(rule, text)
        .map_err(|source| ParserError::Pest {
            source: Box::new(source),
        })
        .and_then(|mut code_pairs| code_pairs.next().ok_or(ParserError::Empty))
}

#[derive(pest_derive::Parser)]
#[grammar = "test.pest"]
pub struct TestParser;

impl TestParser {
    pub fn parse(text: &str) -> Result<Pair<'_, Rule>, ParserError<Rule>> {
        parse(text, Rule::file, PhantomData::<Self>)
    }
}

#[cfg(test)]
mod tests {
    use super::{ParserError, Rule, TestParser};
    use indoc::indoc;
    use pest::iterators::Pairs;

    fn assert_nonterminal<'a>(pairs: &mut Pairs<'a, Rule>, expected_name: &str) -> Pairs<'a, Rule> {
        let expression = pairs.next().expect("Missing expression");
        assert_eq!(expression.as_rule(), Rule::expression);
        let mut pairs = expression.into_inner();
        let rule_name = pairs.next().expect("Missing identifier");
        assert_eq!(rule_name.as_rule(), Rule::identifier);
        assert_eq!(rule_name.as_str(), expected_name);
        let subexpressions = pairs.next().expect("Missing subexpressions");
        assert_eq!(subexpressions.as_rule(), Rule::sub_expressions);
        subexpressions.into_inner()
    }

    fn assert_terminal<'a>(
        pairs: &mut Pairs<'a, Rule>,
        expected_name: &str,
        expected_value: Option<&str>,
    ) {
        let expression = pairs.next().expect("Missing expression");
        assert_eq!(expression.as_rule(), Rule::expression);
        let mut pairs = expression.into_inner();
        let rule_name = pairs.next().expect("Missing identifier");
        assert_eq!(rule_name.as_rule(), Rule::identifier);
        assert_eq!(rule_name.as_str(), expected_name);
        match (pairs.next(), expected_value) {
            (Some(value_str), Some(expected)) => {
                assert_eq!(value_str.as_rule(), Rule::string);
                assert_eq!(value_str.as_rule(), Rule::string);
                let mut pairs = value_str.into_inner();
                let value = pairs.next().expect("Missing value");
                assert_eq!(value.as_rule(), Rule::string_value);
                assert_eq!(value.as_str(), expected);
            }
            (Some(value_str), None) => panic!(
                "Terminal node has value {:?} but there is no expected value",
                value_str
            ),
            (None, Some(expected)) => {
                panic!("Terminal node has no value but expected {expected}")
            }
            _ => (),
        }
    }

    #[test]
    fn test_parse() -> Result<(), ParserError<Rule>> {
        let text = indoc! {r#"
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

        let root = TestParser::parse(text)?;
        let mut root_pairs = root.into_inner();
        let test_case = root_pairs.next().expect("Missing test case");
        let mut test_case_pairs = test_case.into_inner();
        let test_name = test_case_pairs.next().expect("Missing test name");
        assert_eq!(test_name.as_rule(), Rule::test_name);
        assert_eq!(test_name.as_str().trim(), "My Test");
        let code_block = test_case_pairs.next().expect("Missing code");
        assert_eq!(code_block.as_rule(), Rule::code_block);
        let mut pairs = code_block.into_inner();
        let div = pairs.next().expect("Missing div");
        assert_eq!(div.as_rule(), Rule::div);
        assert_eq!(div.as_str().trim(), "=======");
        let code = pairs.next().expect("Missing code");
        assert_eq!(code.as_rule(), Rule::code);
        assert_eq!(code.as_str().trim(), "fn x() int {\n  return 1;\n}");
        let mut pairs = assert_nonterminal(&mut test_case_pairs, "source_file");
        let mut pairs = assert_nonterminal(&mut pairs, "function_definition");
        assert_terminal(&mut pairs, "identifier", Some("x"));
        assert_terminal(&mut pairs, "parameter_list", None);
        assert_terminal(&mut pairs, "primitive_type", Some("int"));
        let mut pairs = assert_nonterminal(&mut pairs, "block");
        let mut pairs = assert_nonterminal(&mut pairs, "return_statement");
        assert_terminal(&mut pairs, "number", Some("1"));
        Ok(())
    }

    #[test]
    fn test_parse_suite() -> Result<(), ParserError<Rule>> {
        let text = indoc! {r#"
        test_one: First test example
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
              (inner_block
                (return_statement
                  (number: "1")
                )
              )
            )
          )
        )
        
        test_two: Second test example
        =======
        fn y() bool {
          return true;
        }
        =======
        (source_file
          (function_definition
            (identifier: "y")
            (parameter_list)
            (primitive_type: "bool")
            (block
              (inner_block
                (return_statement
                  (boolean: "true")
                )
              )
            )
          )
        )
        "#};
        let root = TestParser::parse(text)?;
        let mut root_pairs = root.into_inner();
        assert_eq!(root_pairs.len(), 3);
        let test_case = root_pairs.next().expect("Missing test case");
        let mut test_case_pairs = test_case.into_inner();
        let test_name = test_case_pairs.next().expect("Missing test name");
        assert_eq!(test_name.as_rule(), Rule::test_name);
        let mut test_name_pairs = test_name.into_inner();
        let test_identifier = test_name_pairs.next().expect("Missing test identifier");
        assert_eq!(test_identifier.as_rule(), Rule::test_identifier);
        assert_eq!(test_identifier.as_str().trim(), "test_one");
        let test_title = test_name_pairs.next().expect("Missing test title");
        assert_eq!(test_title.as_rule(), Rule::test_title);
        assert_eq!(test_title.as_str().trim(), "First test example");
        let code_block = test_case_pairs.next().expect("Missing code block");
        assert_eq!(code_block.as_rule(), Rule::code_block);
        let mut pairs = code_block.into_inner();
        let div = pairs.next().expect("Missing div");
        assert_eq!(div.as_rule(), Rule::div);
        assert_eq!(div.as_str().trim(), "=======");
        let code = pairs.next().expect("Missing code");
        assert_eq!(code.as_rule(), Rule::code);
        assert_eq!(code.as_str().trim(), "fn x() int {\n  return 1;\n}");
        let mut pairs = assert_nonterminal(&mut test_case_pairs, "source_file");
        let mut pairs = assert_nonterminal(&mut pairs, "function_definition");
        assert_terminal(&mut pairs, "identifier", Some("x"));
        assert_terminal(&mut pairs, "parameter_list", None);
        assert_terminal(&mut pairs, "primitive_type", Some("int"));
        let mut pairs = assert_nonterminal(&mut pairs, "block");
        let mut pairs = assert_nonterminal(&mut pairs, "inner_block");
        let mut pairs = assert_nonterminal(&mut pairs, "return_statement");
        assert_terminal(&mut pairs, "number", Some("1"));

        // Second test case
        let test_case = root_pairs.next().expect("Missing test case");
        let mut test_case_pairs = test_case.into_inner();
        let test_name = test_case_pairs.next().expect("Missing test name");
        assert_eq!(test_name.as_rule(), Rule::test_name);
        let mut test_name_pairs = test_name.into_inner();
        let test_identifier = test_name_pairs.next().expect("Missing test identifier");
        assert_eq!(test_identifier.as_rule(), Rule::test_identifier);
        assert_eq!(test_identifier.as_str().trim(), "test_two");
        let test_title = test_name_pairs.next().expect("Missing test title");
        assert_eq!(test_title.as_rule(), Rule::test_title);
        assert_eq!(test_title.as_str().trim(), "Second test example");
        let code_block = test_case_pairs.next().expect("Missing code block");
        assert_eq!(code_block.as_rule(), Rule::code_block);
        let mut pairs = code_block.into_inner();
        let div = pairs.next().expect("Missing div");
        assert_eq!(div.as_rule(), Rule::div);
        assert_eq!(div.as_str().trim(), "=======");
        let code = pairs.next().expect("Missing code");
        assert_eq!(code.as_rule(), Rule::code);
        assert_eq!(code.as_str().trim(), "fn y() bool {\n  return true;\n}");
        let mut pairs = assert_nonterminal(&mut test_case_pairs, "source_file");
        let mut pairs = assert_nonterminal(&mut pairs, "function_definition");
        assert_terminal(&mut pairs, "identifier", Some("y"));
        assert_terminal(&mut pairs, "parameter_list", None);
        assert_terminal(&mut pairs, "primitive_type", Some("bool"));
        let mut pairs = assert_nonterminal(&mut pairs, "block");
        let mut pairs = assert_nonterminal(&mut pairs, "inner_block");
        let mut pairs = assert_nonterminal(&mut pairs, "return_statement");
        assert_terminal(&mut pairs, "boolean", Some("true"));
        Ok(())
    }

    #[test]
    fn test_parse_suite_single_test() -> Result<(), ParserError<Rule>> {
        let text = indoc! {r#"
        test_one: First test example
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
              (inner_block
                (return_statement
                  (number: "1")
                )
              )
            )
          )
        )
        "#};
        let root = TestParser::parse(text)?;
        let mut root_pairs = root.into_inner();
        assert_eq!(root_pairs.len(), 2);
        let test_case = root_pairs.next().expect("Missing test case");
        let mut test_case_pairs = test_case.into_inner();
        let test_name = test_case_pairs.next().expect("Missing test name");
        assert_eq!(test_name.as_rule(), Rule::test_name);
        let mut test_name_pairs = test_name.into_inner();
        let test_identifier = test_name_pairs.next().expect("Missing test identifier");
        assert_eq!(test_identifier.as_rule(), Rule::test_identifier);
        assert_eq!(test_identifier.as_str().trim(), "test_one");
        let test_title = test_name_pairs.next().expect("Missing test title");
        assert_eq!(test_title.as_rule(), Rule::test_title);
        assert_eq!(test_title.as_str().trim(), "First test example");
        let code_block = test_case_pairs.next().expect("Missing code block");
        assert_eq!(code_block.as_rule(), Rule::code_block);
        let mut pairs = code_block.into_inner();
        let div = pairs.next().expect("Missing div");
        assert_eq!(div.as_rule(), Rule::div);
        assert_eq!(div.as_str().trim(), "=======");
        let code = pairs.next().expect("Missing code");
        assert_eq!(code.as_rule(), Rule::code);
        assert_eq!(code.as_str().trim(), "fn x() int {\n  return 1;\n}");
        let mut pairs = assert_nonterminal(&mut test_case_pairs, "source_file");
        let mut pairs = assert_nonterminal(&mut pairs, "function_definition");
        assert_terminal(&mut pairs, "identifier", Some("x"));
        assert_terminal(&mut pairs, "parameter_list", None);
        assert_terminal(&mut pairs, "primitive_type", Some("int"));
        let mut pairs = assert_nonterminal(&mut pairs, "block");
        let mut pairs = assert_nonterminal(&mut pairs, "inner_block");
        let mut pairs = assert_nonterminal(&mut pairs, "return_statement");
        assert_terminal(&mut pairs, "number", Some("1"));
        Ok(())
    }

    #[test]
    fn test_parse_suite_single_test_no_identifier() -> Result<(), ParserError<Rule>> {
        let text = indoc! {r#"
        First test example
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
              (inner_block
                (return_statement
                  (number: "1")
                )
              )
            )
          )
        )
        "#};
        let root = TestParser::parse(text)?;
        let mut root_pairs = root.into_inner();
        assert_eq!(root_pairs.len(), 2);
        let test_case = root_pairs.next().expect("Missing test case");
        let mut test_case_pairs = test_case.into_inner();
        let test_name = test_case_pairs.next().expect("Missing test name");
        assert_eq!(test_name.as_rule(), Rule::test_name);
        let mut test_name_pairs = test_name.into_inner();
        let test_title = test_name_pairs.next().expect("Missing test title");
        assert_eq!(test_title.as_rule(), Rule::test_title);
        assert_eq!(test_title.as_str().trim(), "First test example");
        let code_block = test_case_pairs.next().expect("Missing code block");
        assert_eq!(code_block.as_rule(), Rule::code_block);
        let mut pairs = code_block.into_inner();
        let div = pairs.next().expect("Missing div");
        assert_eq!(div.as_rule(), Rule::div);
        assert_eq!(div.as_str().trim(), "=======");
        let code = pairs.next().expect("Missing code");
        assert_eq!(code.as_rule(), Rule::code);
        assert_eq!(code.as_str().trim(), "fn x() int {\n  return 1;\n}");
        let mut pairs = assert_nonterminal(&mut test_case_pairs, "source_file");
        let mut pairs = assert_nonterminal(&mut pairs, "function_definition");
        assert_terminal(&mut pairs, "identifier", Some("x"));
        assert_terminal(&mut pairs, "parameter_list", None);
        assert_terminal(&mut pairs, "primitive_type", Some("int"));
        let mut pairs = assert_nonterminal(&mut pairs, "block");
        let mut pairs = assert_nonterminal(&mut pairs, "inner_block");
        let mut pairs = assert_nonterminal(&mut pairs, "return_statement");
        assert_terminal(&mut pairs, "number", Some("1"));
        Ok(())
    }
}
