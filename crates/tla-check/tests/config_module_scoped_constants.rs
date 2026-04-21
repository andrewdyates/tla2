// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_check::Config;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn parse_module_scoped_constant_entries_go_to_module_maps() {
    let input = r#"
INIT Init
NEXT Next
CONSTANT FooNoSpace <- [Mod]Bar
CONSTANT FooSpace <- [Mod] Bar
CONSTANT BazSpace = [Mod] {1, 2}
CONSTANT BazNoSpace = [Mod]{1,2}
CONSTANT Server <- [ model value ]
"#;
    let config = Config::parse(input).unwrap();

    assert!(!config.constants.contains_key("FooNoSpace"));
    assert!(!config.constants.contains_key("FooSpace"));
    assert!(!config.constants.contains_key("BazSpace"));
    assert!(!config.constants.contains_key("BazNoSpace"));
    assert!(matches!(
        config.constants.get("Server"),
        Some(tla_check::ConstantValue::ModelValue)
    ));

    assert_eq!(
        config
            .module_overrides
            .get("Mod")
            .and_then(|m| m.get("FooNoSpace"))
            .map(String::as_str),
        Some("Bar")
    );
    assert_eq!(
        config
            .module_assignments
            .get("Mod")
            .and_then(|m| m.get("BazSpace"))
            .map(String::as_str),
        Some("{1, 2}")
    );

    assert_eq!(
        config
            .module_overrides
            .get("Mod")
            .and_then(|m| m.get("FooSpace"))
            .map(String::as_str),
        Some("Bar")
    );
    assert_eq!(
        config
            .module_assignments
            .get("Mod")
            .and_then(|m| m.get("BazNoSpace"))
            .map(String::as_str),
        Some("{1,2}")
    );
}
