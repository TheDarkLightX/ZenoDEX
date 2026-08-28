from tools.check_rust_fcis_policy import scan_source


def test_scanner_finds_authority_forbidden_constructs():
    findings = scan_source(
        "core.rs",
        "pub fn step(state: &mut ValidatedState, x: Option<String>) -> Result<u8, &'static str> { x.unwrap(); Ok(1) }",
    )
    assert {finding.rule for finding in findings} == {
        "PANIC_ESCAPE",
        "PUBLIC_MUT_STATE",
        "RAW_STRING_REJECT",
        "RAW_WIRE_NUMERIC",
    }


def test_scanner_excludes_cfg_test_module():
    findings = scan_source(
        "core.rs",
        "pub fn checked() -> Result<(), Error> { Ok(()) }\n#[cfg(test)]\nmod tests { fn helper() { panic!(\"test\") } }\n",
    )
    assert findings == ()
