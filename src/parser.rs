use pest::{error::Error, iterators::Pair, Parser, RuleType};
use pest_derive;
use std::marker::PhantomData;

#[derive(Debug)]
pub enum ParserError<R> {
    Pest { source: Error<R> },
    Empty,
}

pub fn parse<'a, R: RuleType, P: Parser<R>>(
    text: &'a str,
    rule: R,
    _: PhantomData<P>,
) -> Result<Pair<'a, R>, ParserError<R>> {
    P::parse(rule, text)
        .map_err(|source| ParserError::Pest { source })
        .and_then(|mut code_pairs| code_pairs.next().ok_or_else(|| ParserError::Empty))
}

#[derive(pest_derive::Parser)]
#[grammar = "test.pest"]
pub struct TestParser;

impl TestParser {
    pub fn parse<'a>(text: &'a str) -> Result<Pair<'a, Rule>, ParserError<Rule>> {
        parse(text, Rule::test_case, PhantomData::<Self>)
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
        let rule_name = pairs.next().expect("Missing rule name");
        assert_eq!(rule_name.as_rule(), Rule::rule_name);
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
        let rule_name = pairs.next().expect("Missing rule name");
        assert_eq!(rule_name.as_rule(), Rule::rule_name);
        assert_eq!(rule_name.as_str(), expected_name);
        match (pairs.next(), expected_value) {
            (Some(value_str), Some(expected)) => {
                assert_eq!(value_str.as_rule(), Rule::rule_value_str);
                assert_eq!(value_str.as_rule(), Rule::rule_value_str);
                let mut pairs = value_str.into_inner();
                let value = pairs.next().expect("Missing value");
                assert_eq!(value.as_rule(), Rule::rule_value);
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
        let test_name = root_pairs.next().expect("Missing test name");
        assert_eq!(test_name.as_rule(), Rule::test_name);
        assert_eq!(test_name.as_str().trim(), "My Test");
        let code_block = root_pairs.next().expect("Missing code");
        assert_eq!(code_block.as_rule(), Rule::code_block);
        let mut pairs = code_block.into_inner();
        let div = pairs.next().expect("Missing div");
        assert_eq!(div.as_rule(), Rule::div);
        assert_eq!(div.as_str().trim(), "=======");
        let code = pairs.next().expect("Missing code");
        assert_eq!(code.as_rule(), Rule::code);
        assert_eq!(code.as_str().trim(), "fn x() int {\n  return 1;\n}");
        let mut pairs = assert_nonterminal(&mut root_pairs, "source_file");
        let mut pairs = assert_nonterminal(&mut pairs, "function_definition");
        assert_terminal(&mut pairs, "identifier", Some("x"));
        assert_terminal(&mut pairs, "parameter_list", None);
        assert_terminal(&mut pairs, "primitive_type", Some("int"));
        let mut pairs = assert_nonterminal(&mut pairs, "block");
        let mut pairs = assert_nonterminal(&mut pairs, "return_statement");
        assert_terminal(&mut pairs, "number", Some("1"));
        Ok(())
    }
}
