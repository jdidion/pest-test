//! Integration tests that exercise the public `PestTester` API end-to-end
//! against a real pest grammar and on-disk test-case fixtures in
//! `tests/pest/`. These cover the success path of `evaluate`/`evaluate_strict`
//! as well as each error variant of `TestError` that is reachable from the
//! public API.

use pest_test::{default_test_dir, PestTester, TestError};
use std::collections::HashSet;

mod example {
    #[derive(pest_derive::Parser)]
    #[grammar = "tests/example.pest"]
    pub struct ExampleParser;
}

use example::{ExampleParser, Rule};

/// Build a tester pointed at `tests/pest` with the default `.txt` extension,
/// skipping the EOI rule (which appears in every parse tree and is never part
/// of the expected s-expression).
fn tester() -> PestTester<Rule, ExampleParser> {
    PestTester::from_defaults(Rule::source_file, HashSet::from([Rule::EOI]))
}

#[test]
fn test_default_test_dir_is_tests_pest() {
    let dir = default_test_dir();
    assert!(dir.ends_with("tests/pest"));
}

#[test]
fn test_evaluate_strict_pass() {
    let tester = tester();
    let result = tester.evaluate_strict("pass");
    assert!(
        result.is_ok(),
        "expected pass.txt to evaluate; got {result:?}"
    );
}

#[test]
fn test_evaluate_lenient_pass() {
    let tester = tester();
    // The lenient flag (ignore_missing_expected_values=true) should also accept
    // the matching tree.
    let result = tester.evaluate("pass", true);
    assert!(
        result.is_ok(),
        "expected pass.txt to evaluate; got {result:?}"
    );
}

#[test]
fn test_evaluate_diff_error() {
    let tester = tester();
    // mismatch.txt expects identifier "y" but the code parses to "x".
    match tester.evaluate_strict("mismatch") {
        Err(TestError::Diff { diff }) => {
            // The diff should be printable in both colorized and plain modes.
            diff.print_test_result(false).expect("plain print failed");
            diff.print_test_result(true)
                .expect("colorized print failed");
        }
        other => panic!("expected TestError::Diff, got {other:?}"),
    }
}

#[test]
fn test_evaluate_target_parser_error() {
    let tester = tester();
    // unparseable.txt holds code that the example grammar cannot parse, which
    // surfaces as TestError::Target.
    match tester.evaluate_strict("unparseable") {
        Err(TestError::Target { source }) => {
            // The wrapped pest error should be displayable.
            let _ = format!("{source}");
        }
        other => panic!("expected TestError::Target, got {other:?}"),
    }
}

#[test]
fn test_evaluate_missing_file_io_error() {
    let tester = tester();
    match tester.evaluate_strict("does-not-exist") {
        Err(TestError::IO { source }) => {
            assert_eq!(source.kind(), std::io::ErrorKind::NotFound);
        }
        other => panic!("expected TestError::IO, got {other:?}"),
    }
}

#[test]
fn test_new_with_custom_dir_and_ext() {
    // Exercise the `new` constructor directly (not just `from_defaults`) with a
    // custom extension. Pointing at the same fixtures but with a non-matching
    // extension should produce an IO (not-found) error.
    let dir = default_test_dir();
    let tester: PestTester<Rule, ExampleParser> =
        PestTester::new(dir, "pest", Rule::source_file, HashSet::from([Rule::EOI]));
    match tester.evaluate_strict("pass") {
        Err(TestError::IO { source }) => {
            assert_eq!(source.kind(), std::io::ErrorKind::NotFound);
        }
        other => panic!("expected TestError::IO for wrong ext, got {other:?}"),
    }
}

#[test]
fn test_test_error_display() {
    // Each TestError Display impl should produce non-empty text. The Diff
    // variant is covered via a real diff; the others via their messages.
    let tester = tester();
    let target = tester.evaluate_strict("unparseable").unwrap_err();
    assert!(format!("{target}").contains("target parser"));
    let io = tester.evaluate_strict("does-not-exist").unwrap_err();
    assert!(format!("{io}").contains("reading test case"));
    let diff = tester.evaluate_strict("mismatch").unwrap_err();
    assert!(format!("{diff}").contains("different"));
}
