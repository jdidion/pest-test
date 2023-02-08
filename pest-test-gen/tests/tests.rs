use pest_test_gen::pest_tests;

mod example {
    use pest_derive;

    #[derive(pest_derive::Parser)]
    #[grammar = "tests/example.pest"]
    pub struct ExampleParser;
}

#[pest_tests(
    super::example::ExampleParser,
    super::example::Rule,
    "source_file",
    lazy_static = true
)]
#[cfg(test)]
mod test_cases {}
