// use this command for ui tests:
// 
// clear;clear; env TRYBUILD=overwrite cargo test --no-default-features \
// --features="__ui_tests"





#[cfg(feature = "__ui_tests")]
#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    for dir in [
        "type_failures_ui",
        "syntax_failures_ui",
        "failing_asserts_ui",
    ] {
        t.compile_fail(format!("tests/misc_tests/{}/*-err.rs", dir));

        t.pass(format!("tests/misc_tests/{}/*fine.rs", dir));
    }
}
