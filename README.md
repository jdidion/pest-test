# pest-test

Testing framework for [pest parser](https://pest.rs) (similar to `tree-sitter test`).

## Test cases

A test case is a text file with three sections:

* The test name must be on the first line of the file. It may contain any characters except newline.
* The source code block is delimited by any sequence of three or more characters. The same sequence of characters must preceed and follow the code block, and that sequence of characters may not appear anywhere within the code block. Any whitespace between the code and the delimiter is trimmed.
* The expected output syntax tree written as an [S-expression](https://en.wikipedia.org/wiki/S-expression). Optionally, a terminal node may be followed by its expected string value.

Here is an example test. Note that the code block delimiter is exactly 7 '=' characters.

```
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

```

## Usage

The main interface to the test framework is `pest_test::PestTester`. By default, tests are assumed to be in the `tests/parser` directory of your crate and have a `.txt` file extension. The example below shows using the `lazy_static` macro to create a single `PestTester` instance and then using it to evaluate any number of tests.

```rust
#[cfg(test)]
mod tests {
  use lazy_static::lazy_static;
  use pest_test::{Error, PestTester};
  use myparser::{MyParser, Rule};

  lazy_static! {
    static ref TESTER: PestTester<Rule, MyParser> = 
      PestTester::from_defaults(Rule::root_rule);
  }

  // Loads test from `tests/parser/mytest.txt` and evaluates it. Returns an `Err<pest_test::Error>`
  // if there was an error evaluating the test, or if the expected and actual values do not match.
  fn test_my_parser -> Result<(), Error> {
    (*tester).evaluate_strict("mytest")
  }
}
```

## Details

Test files are parsed using pest. The source code is parsed using your pest grammar, and the resulting tree is iterated exhaustively to build up a nested data structure, which is then matched to the same structure built from the expected output. If they don't match, the tree is printed with the differences in-line.