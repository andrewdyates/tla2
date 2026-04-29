// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Registry for type-specialized record structs.
//!
//! When type inference determines that a record has statically-known field names
//! and resolved field types, this registry generates a Rust struct definition
//! instead of using `TlaRecord<Value>`. This provides:
//! - Named field access (`.field` instead of `.get("field")`)
//! - Type safety at the Rust level
//! - Better generated code readability

use super::TlaType;
use std::collections::BTreeMap;
use std::fmt::Write;

/// A single generated struct definition for a record with known fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedStruct {
    /// The PascalCase struct name (e.g., `RecordAbCount`).
    pub name: String,
    /// Sorted field names mapped to their Rust types.
    /// Sorted by field name for deterministic output.
    pub fields: Vec<(String, TlaType)>,
}

impl GeneratedStruct {
    /// Emit the Rust struct definition as a string.
    pub fn emit_definition(&self) -> String {
        let mut out = String::new();
        writeln!(
            out,
            "#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]"
        )
        .expect("write to String");
        writeln!(out, "pub struct {} {{", self.name).expect("write to String");
        for (field_name, field_type) in &self.fields {
            let snake = field_to_snake_case(field_name);
            writeln!(out, "    pub {}: {},", snake, field_type.to_rust_type())
                .expect("write to String");
        }
        writeln!(out, "}}").expect("write to String");
        out
    }

    /// Emit the Rust struct definition, using struct names from the registry
    /// for nested record types instead of `TlaRecord<T>`.
    pub fn emit_definition_with_structs(&self, registry: &StructRegistry) -> String {
        let mut out = String::new();
        writeln!(
            out,
            "#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]"
        )
        .expect("write to String");
        writeln!(out, "pub struct {} {{", self.name).expect("write to String");
        for (field_name, field_type) in &self.fields {
            let snake = field_to_snake_case(field_name);
            writeln!(
                out,
                "    pub {}: {},",
                snake,
                field_type.to_rust_type_with_structs(registry)
            )
            .expect("write to String");
        }
        writeln!(out, "}}").expect("write to String");
        out
    }
}

/// Registry that collects record types and produces struct definitions.
///
/// Each unique set of (field_name, field_type) pairs maps to one generated struct.
/// The registry deduplicates: if two record expressions have the same fields and
/// types, they share the same struct.
#[derive(Debug, Clone, Default)]
pub struct StructRegistry {
    /// Map from canonical key (sorted field names + types) to generated struct.
    structs: BTreeMap<String, GeneratedStruct>,
}

impl StructRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Check whether a `TlaType::Record` has statically-known, fully-resolved fields
    /// suitable for struct generation. Returns the struct name if registered (or
    /// registers and returns it).
    ///
    /// Returns `None` if:
    /// - The record has no fields
    /// - Any field type is unresolved (`Var` or `Unknown`)
    pub fn try_register_record(&mut self, fields: &[(String, TlaType)]) -> Option<String> {
        if fields.is_empty() {
            return None;
        }
        // All field types must be fully resolved
        if !fields.iter().all(|(_, t)| t.is_resolved()) {
            return None;
        }

        let key = canonical_key(fields);
        if let Some(existing) = self.structs.get(&key) {
            return Some(existing.name.clone());
        }

        let name = generate_struct_name(fields);
        let mut sorted_fields: Vec<_> = fields.to_vec();
        sorted_fields.sort_by(|a, b| a.0.cmp(&b.0));

        self.structs.insert(
            key,
            GeneratedStruct {
                name: name.clone(),
                fields: sorted_fields,
            },
        );
        Some(name)
    }

    /// Look up a previously registered record type without registering it.
    pub fn lookup_record(&self, fields: &[(String, TlaType)]) -> Option<&GeneratedStruct> {
        if fields.is_empty() {
            return None;
        }
        let key = canonical_key(fields);
        self.structs.get(&key)
    }

    /// Return all registered structs, sorted by name for deterministic output.
    pub fn all_structs(&self) -> Vec<&GeneratedStruct> {
        let mut out: Vec<_> = self.structs.values().collect();
        out.sort_by(|a, b| a.name.cmp(&b.name));
        out
    }

    /// Emit all struct definitions as a single string block.
    ///
    /// Uses struct names from this registry for nested record types, so that
    /// `Set<[a |-> Int, b |-> Bool]>` renders as `TlaSet<RecordAIntBBool>`
    /// instead of `TlaSet<TlaRecord<i64>>`.
    pub fn emit_all_definitions(&self) -> String {
        let mut out = String::new();
        for s in self.all_structs() {
            out.push_str(&s.emit_definition_with_structs(self));
            out.push('\n');
        }
        out
    }

    /// Returns true if there are any registered structs.
    pub fn has_structs(&self) -> bool {
        !self.structs.is_empty()
    }
}

/// Build a canonical key from record fields for deduplication.
/// Sorts by field name so that `[a |-> 1, b |-> 2]` and `[b |-> 2, a |-> 1]`
/// produce the same key.
fn canonical_key(fields: &[(String, TlaType)]) -> String {
    let mut pairs: Vec<_> = fields
        .iter()
        .map(|(name, ty)| format!("{}:{}", name, ty.to_rust_type()))
        .collect();
    pairs.sort();
    pairs.join(",")
}

/// Generate a PascalCase struct name from field names and types.
/// E.g., fields `[("count", Int), ("name", Str)]` -> `RecordCountIntNameStr`.
/// Types are included to disambiguate records with same field names but different types.
fn generate_struct_name(fields: &[(String, TlaType)]) -> String {
    let mut sorted: Vec<_> = fields.to_vec();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));

    let mut name = "Record".to_string();
    for (field_name, field_type) in &sorted {
        let mut chars = field_name.chars();
        if let Some(first) = chars.next() {
            name.push(first.to_ascii_uppercase());
            name.extend(chars);
        }
        let type_suffix = match field_type {
            TlaType::Int => "Int",
            TlaType::Bool => "Bool",
            TlaType::String => "Str",
            _ => "V",
        };
        name.push_str(type_suffix);
    }
    name
}

/// Convert a TLA+ field name to a valid Rust snake_case identifier.
pub fn field_to_snake_case(field: &str) -> String {
    let mut result = String::new();
    for c in field.chars() {
        if c.is_ascii_alphanumeric() {
            if c.is_uppercase() && !result.is_empty() && !result.ends_with('_') {
                result.push('_');
            }
            result.push(c.to_ascii_lowercase());
        } else {
            if !result.is_empty() && !result.ends_with('_') {
                result.push('_');
            }
        }
    }
    while result.ends_with('_') {
        result.pop();
    }
    if result.is_empty() {
        "_field".to_string()
    } else if result.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{result}")
    } else {
        // Avoid Rust keywords
        match result.as_str() {
            "type" | "self" | "super" | "crate" | "mod" | "fn" | "let" | "mut" | "ref"
            | "match" | "if" | "else" | "for" | "while" | "loop" | "return" | "break"
            | "continue" | "struct" | "enum" | "trait" | "impl" | "use" | "pub" | "where"
            | "async" | "await" | "move" | "in" | "as" | "true" | "false" => {
                format!("r#{result}")
            }
            _ => result,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_register_simple_record() {
        let mut reg = StructRegistry::new();
        let fields = vec![
            ("a".to_string(), TlaType::Int),
            ("b".to_string(), TlaType::Bool),
        ];
        let name = reg.try_register_record(&fields);
        assert_eq!(name, Some("RecordAIntBBool".to_string()));

        // Same fields in different order should return same struct
        let fields_rev = vec![
            ("b".to_string(), TlaType::Bool),
            ("a".to_string(), TlaType::Int),
        ];
        let name2 = reg.try_register_record(&fields_rev);
        assert_eq!(name2, Some("RecordAIntBBool".to_string()));
        assert_eq!(reg.all_structs().len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_register_rejects_unresolved() {
        let mut reg = StructRegistry::new();
        let fields = vec![
            ("x".to_string(), TlaType::Int),
            ("y".to_string(), TlaType::Unknown),
        ];
        assert_eq!(reg.try_register_record(&fields), None);

        let fields_var = vec![
            ("x".to_string(), TlaType::Int),
            ("y".to_string(), TlaType::Var(0)),
        ];
        assert_eq!(reg.try_register_record(&fields_var), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_register_rejects_empty() {
        let mut reg = StructRegistry::new();
        assert_eq!(reg.try_register_record(&[]), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_emit_definition() {
        let mut reg = StructRegistry::new();
        let fields = vec![
            ("count".to_string(), TlaType::Int),
            ("active".to_string(), TlaType::Bool),
        ];
        reg.try_register_record(&fields);

        let defs = reg.emit_all_definitions();
        assert!(defs.contains("pub struct RecordActiveBoolCountInt"));
        assert!(defs.contains("pub active: bool,"));
        assert!(defs.contains("pub count: i64,"));
        assert!(defs.contains("#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_different_types_different_structs() {
        let mut reg = StructRegistry::new();
        let fields1 = vec![
            ("x".to_string(), TlaType::Int),
            ("y".to_string(), TlaType::Int),
        ];
        let fields2 = vec![
            ("x".to_string(), TlaType::Int),
            ("y".to_string(), TlaType::Bool),
        ];
        let name1 = reg.try_register_record(&fields1);
        let name2 = reg.try_register_record(&fields2);
        // Same field names but different types: different canonical key, different struct
        assert_ne!(name1, name2);
        assert_eq!(reg.all_structs().len(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_field_to_snake_case() {
        assert_eq!(field_to_snake_case("myField"), "my_field");
        assert_eq!(field_to_snake_case("count"), "count");
        assert_eq!(field_to_snake_case("ABC"), "a_b_c");
        assert_eq!(field_to_snake_case("type"), "r#type");
        assert_eq!(field_to_snake_case("123abc"), "_123abc");
    }
}
