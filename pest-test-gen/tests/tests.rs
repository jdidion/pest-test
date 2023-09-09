use pest_test_gen::pest_tests;

mod example {
    use pest_derive;

    #[derive(pest_derive::Parser)]
    #[grammar = "tests/example.pest"]
    pub struct ExampleParser;
}

#[pest_tests(super::example::ExampleParser, super::example::Rule, "source_file")]
#[cfg(test)]
mod example_test_cases {}

#[pest_tests(
    super::example::ExampleParser,
    super::example::Rule,
    "source_file",
    lazy_static = true
)]
#[cfg(test)]
mod example_test_cases_lazy_static {}

mod csv {
    use pest_derive;

    #[derive(pest_derive::Parser)]
    #[grammar = "tests/csv.pest"]
    pub struct CsvParser;
}

#[pest_tests(super::csv::CsvParser, super::csv::Rule, "file", dir = "tests/csv_cases")]
#[cfg(test)]
mod csv_test_cases {}

#[pest_tests(
    super::csv::CsvParser,
    super::csv::Rule,
    "file",
    lazy_static = true,
    dir = "tests/csv_cases"
)]
#[cfg(test)]
mod csv_test_cases_lazy_static {}
