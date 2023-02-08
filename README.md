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

The main interface to the test framework is `pest_test::PestTester`. By default, tests are assumed to be in the `tests/pest` directory of your crate and have a `.txt` file extension. The example below shows using the `lazy_static` macro to create a single `PestTester` instance and then using it to evaluate any number of tests.

```rust
#[cfg(test)]
mod tests {
  use mycrate::parser::{MyParser, Rule};
  use lazy_static::lazy_static;
  use pest_test::{Error, PestTester};

  lazy_static! {
    static ref TESTER: PestTester<Rule, MyParser> = 
      PestTester::from_defaults(Rule::root_rule);
  }

  // Loads test from `tests/pest/mytest.txt` and evaluates it. Returns an `Err<pest_test::Error>`
  // if there was an error evaluating the test, or if the expected and actual values do not match.
  fn test_my_parser -> Result<(), Error> {
    (*TESTER).evaluate_strict("mytest")
  }
}
```

If you add `pest-test-gen` as a dev dependency, then you can use the `pest_tests` attribute macro to generate tests for all your test cases:

```rust
// Generate tests for all test cases in tests/pest/foo/ and all subdirectories. Since
// `lazy_static = true`, a single `PestTester` is created and used by all tests; otherwise a new
// `PestTester` would be created for each test.
#[pest_tests(
  mycrate::parser::MyParser,
  mycrate::parser::Rule,
  "root_rule",
  subdir = "foo",
  recursive = true,
  lazy_static = true,
)]
#[cfg(test)]
mod foo_tests {}
```

Note that a test module is only recompiled when its code changes. Thus, if you add or rename a test case in `tests/pest` without changing the test module, the test module might not get updated to include the new/renamed tests, so you may need to delete the `target` folder to force your tests to be recompiled.

## Details

Test files are parsed using pest. The source code is parsed using your pest grammar, and the resulting tree is iterated exhaustively to build up a nested data structure, which is then matched to the same structure built from the expected output. If they don't match, the tree is printed with the differences in-line.