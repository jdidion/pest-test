# AGENTS.md: pest-test

Testing framework for [pest](https://pest.rs) parsers (analogous to `tree-sitter test`).

## Layout

Cargo workspace with two crates:

- `pest-test/`: the library. Parses `.txt` test cases, runs them through a target
  pest grammar, and diffs the resulting parse tree against an expected S-expression.
  - `src/parser.rs`: parses the test-case file format (grammar in `src/test.pest`).
  - `src/model.rs`: the `Expression` / `TestCase` model and the S-expression formatter.
  - `src/diff.rs`: `ExpressionDiff`, tree comparison and colorized diff rendering.
  - `src/lib.rs`: the public `PestTester` API (`new`, `from_defaults`, `evaluate`,
    `evaluate_strict`) and the `TestError` enum.
- `pest-test-gen/`: a proc-macro crate (`#[pest_tests(...)]`) that generates one
  `#[test]` per on-disk test case.

Trunk branch is `main`.

## Build / test

```sh
cargo build --workspace
cargo test --workspace
```

CI (`.github/workflows/test.yml`) additionally enforces:

```sh
cargo fmt --all -- --check
cargo clippy -- -D warnings
```

Run both locally before pushing: `clippy -D warnings` and an unformatted file will
fail CI.

## Coverage

Measured with [`cargo-llvm-cov`](https://github.com/taiki-e/cargo-llvm-cov):

```sh
cargo llvm-cov --workspace --summary-only
cargo llvm-cov report --show-missing-lines   # per-file uncovered line numbers
```

On a Homebrew rust toolchain that lacks `llvm-profdata`, run coverage under a rustup
toolchain that ships the LLVM tools instead, e.g.:

```sh
rustup run <toolchain> cargo llvm-cov --workspace --summary-only
```

### Test layout

- Module-level unit tests live in `#[cfg(test)] mod tests` blocks inside each `src/*.rs`
  file (they have access to crate-private items such as `assert_rule` and the
  `ExpressionFormatter` fields).
- End-to-end tests of the public `PestTester` API live in `pest-test/tests/integration.rs`
  and drive a real grammar (`pest-test/tests/example.pest`) against fixtures in
  `pest-test/tests/pest/`.
- The proc-macro is exercised by `pest-test-gen/tests/tests.rs`, which uses the
  `#[pest_tests(...)]` attribute against the grammars and fixtures under
  `pest-test-gen/tests/`.

Remaining uncovered code is concentrated in `pest-test-gen` (proc-macro
argument-parsing `abort!` paths, which need a compile-fail harness such as `trybuild`)
and a few provably-unreachable defensive `panic!`s.

## Release

Releases are managed by `release-plz` (`release-plz.toml`); versions are per-crate in
each `Cargo.toml`. Publishing to crates.io is a maintainer action: do not publish
from an agent session.
