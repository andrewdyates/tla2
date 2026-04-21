// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 import` -- import specifications from other formats into TLA+.
//!
//! Supported: JsonStateMachine, Promela (.pml), Alloy (.als).

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::Deserialize;

/// Source format for the import command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ImportFormat {
    JsonStateMachine,
    Promela,
    Alloy,
}

/// Read `file` in `from_format`, emit TLA+ (and optionally .cfg) to `output`.
pub(crate) fn cmd_import(file: &Path, from_format: ImportFormat, output: Option<&Path>) -> Result<()> {
    let content =
        std::fs::read_to_string(file).with_context(|| format!("Failed to read {}", file.display()))?;
    let (tla, cfg) = match from_format {
        ImportFormat::JsonStateMachine => import_json_sm(&content, file)?,
        ImportFormat::Promela => import_promela(&content, file)?,
        ImportFormat::Alloy => import_alloy(&content, file)?,
    };
    write_output(output, tla.as_bytes())?;
    if let (Some(out), Some(cfg)) = (output, cfg) {
        let cfg_path = out.with_extension("cfg");
        std::fs::write(&cfg_path, cfg.as_bytes())
            .with_context(|| format!("Failed to write {}", cfg_path.display()))?;
        eprintln!("Wrote config to {}", cfg_path.display());
    }
    Ok(())
}

#[derive(Debug, Deserialize)]
struct JsonStateMachine {
    name: String,
    variables: BTreeMap<String, String>,
    init: BTreeMap<String, serde_json::Value>,
    transitions: Vec<JsonTransition>,
    #[serde(default)]
    invariants: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct JsonTransition {
    name: String,
    guard: String,
    effect: BTreeMap<String, serde_json::Value>,
}

fn import_json_sm(content: &str, file: &Path) -> Result<(String, Option<String>)> {
    let sm: JsonStateMachine = serde_json::from_str(content)
        .with_context(|| format!("Failed to parse JSON from {}", file.display()))?;
    let vars: Vec<&str> = sm.variables.keys().map(String::as_str).collect();
    if vars.is_empty() {
        bail!("JSON state machine has no variables");
    }
    let mut o = String::new();
    o.push_str(&format!("---- MODULE {} ----\n", sm.name));
    o.push_str("EXTENDS Integers, Sequences, FiniteSets, TLC\n\n");
    o.push_str(&format!("VARIABLE {}\n", vars.join(", ")));
    o.push_str(&format!("\nvars == <<{}>>\n", vars.join(", ")));
    // Init
    o.push_str("\nInit ==\n");
    for (i, v) in vars.iter().enumerate() {
        let val = sm.init.get(*v).map(json_val_to_tla).unwrap_or_else(|| "<<>>".into());
        let pfx = if i == 0 { "    " } else { "    /\\ " };
        o.push_str(&format!("{pfx}{v} = {val}\n"));
    }
    // Transitions
    let mut actions = Vec::new();
    for tr in &sm.transitions {
        actions.push(tr.name.clone());
        o.push_str(&format!("\n{} ==\n    /\\ {}\n", tr.name, tr.guard));
        let changed: Vec<&str> = tr.effect.keys().map(String::as_str).collect();
        for (k, v) in &tr.effect {
            o.push_str(&format!("    /\\ {k}' = {}\n", effect_val(v)));
        }
        let unch: Vec<&&str> = vars.iter().filter(|v| !changed.contains(v)).collect();
        if !unch.is_empty() {
            let u = if unch.len() == 1 {
                unch[0].to_string()
            } else {
                format!("<<{}>>", unch.iter().map(|v| **v).collect::<Vec<_>>().join(", "))
            };
            o.push_str(&format!("    /\\ UNCHANGED {u}\n"));
        }
    }
    // Next + Spec
    o.push_str("\nNext ==\n");
    if actions.is_empty() {
        o.push_str("    UNCHANGED vars\n");
    } else {
        for (i, a) in actions.iter().enumerate() {
            let pfx = if i == 0 { "    " } else { "    \\/ " };
            o.push_str(&format!("{pfx}{a}\n"));
        }
    }
    o.push_str("\nSpec == Init /\\ [][Next]_vars\n");
    for (i, inv) in sm.invariants.iter().enumerate() {
        o.push_str(&format!("\nInv{} == {inv}\n", i + 1));
    }
    let tc: Vec<String> = sm.variables.iter().filter_map(|(n, t)| type_constraint(n, t)).collect();
    if !tc.is_empty() {
        o.push_str("\nTypeOK ==\n");
        for (i, c) in tc.iter().enumerate() {
            let pfx = if i == 0 { "    " } else { "    /\\ " };
            o.push_str(&format!("{pfx}{c}\n"));
        }
    }
    o.push_str("\n====\n");
    let mut cfg = String::from("INIT Init\nNEXT Next\n");
    for (i, _) in sm.invariants.iter().enumerate() {
        cfg.push_str(&format!("INVARIANT Inv{}\n", i + 1));
    }
    if !tc.is_empty() { cfg.push_str("INVARIANT TypeOK\n"); }
    Ok((o, Some(cfg)))
}

fn json_val_to_tla(v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::Null => "<<>>".into(),
        serde_json::Value::Bool(b) => if *b { "TRUE" } else { "FALSE" }.into(),
        serde_json::Value::Number(n) => n.to_string(),
        serde_json::Value::String(s) => format!("\"{s}\""),
        serde_json::Value::Array(a) =>
            format!("<<{}>>", a.iter().map(json_val_to_tla).collect::<Vec<_>>().join(", ")),
        serde_json::Value::Object(m) =>
            format!("[{}]", m.iter().map(|(k, v)| format!("{k} |-> {}", json_val_to_tla(v))).collect::<Vec<_>>().join(", ")),
    }
}

fn effect_val(v: &serde_json::Value) -> String {
    if let serde_json::Value::String(s) = v { s.clone() } else { json_val_to_tla(v) }
}

fn type_constraint(name: &str, ty: &str) -> Option<String> {
    match ty {
        "integer" | "int" => Some(format!("{name} \\in Int")),
        "natural" | "nat" => Some(format!("{name} \\in Nat")),
        "boolean" | "bool" => Some(format!("{name} \\in BOOLEAN")),
        "string" => Some(format!("{name} \\in STRING")),
        _ => None,
    }
}

struct PSpec { name: String, procs: Vec<PProc>, chans: Vec<PChan>, globals: Vec<PVar> }
struct PProc { name: String, body: Vec<String> }
struct PChan { name: String, capacity: usize, msg_type: String }
struct PVar { name: String, type_name: String, init: Option<String> }

fn import_promela(content: &str, file: &Path) -> Result<(String, Option<String>)> {
    let spec = parse_promela(content, file)?;
    let mut all_vars: Vec<String> = spec.globals.iter().map(|v| v.name.clone()).collect();
    for ch in &spec.chans { all_vars.push(ch.name.clone()); }
    for p in &spec.procs { all_vars.push(format!("pc_{}", p.name)); }
    if all_vars.is_empty() { all_vars.push("pc".into()); }

    let mut o = String::new();
    o.push_str(&format!("---- MODULE {} ----\n", spec.name));
    o.push_str("EXTENDS Integers, Sequences, FiniteSets, TLC\n\n");
    o.push_str(&format!("VARIABLE {}\n\nvars == <<{}>>\n", all_vars.join(", "), all_vars.join(", ")));
    // Init
    o.push_str("\nInit ==\n");
    let mut inits: Vec<String> = Vec::new();
    for v in &spec.globals { inits.push(format!("{} = {}", v.name, v.init.as_deref().unwrap_or("0"))); }
    for ch in &spec.chans { inits.push(format!("{} = <<>>", ch.name)); }
    for p in &spec.procs { inits.push(format!("pc_{} = \"ready\"", p.name)); }
    if inits.is_empty() { inits.push("pc = \"ready\"".into()); }
    for (i, c) in inits.iter().enumerate() {
        let pfx = if i == 0 { "    " } else { "    /\\ " };
        o.push_str(&format!("{pfx}{c}\n"));
    }
    // Proctype actions
    for p in &spec.procs {
        o.push_str(&format!("\n{}_step ==\n", p.name));
        o.push_str(&format!("    /\\ pc_{} = \"ready\"\n    /\\ pc_{}' = \"done\"\n", p.name, p.name));
        for line in &p.body {
            let t = line.trim();
            if !t.is_empty() { o.push_str(&format!("    \\* {t}\n")); }
        }
        let others: Vec<&str> = all_vars.iter()
            .filter(|v| *v != &format!("pc_{}", p.name)).map(String::as_str).collect();
        if !others.is_empty() {
            let u = if others.len() == 1 { others[0].to_string() }
                    else { format!("<<{}>>", others.join(", ")) };
            o.push_str(&format!("    /\\ UNCHANGED {u}\n"));
        }
    }
    // Next + Spec
    o.push_str("\nNext ==\n");
    if spec.procs.is_empty() {
        o.push_str("    UNCHANGED vars\n");
    } else {
        for (i, p) in spec.procs.iter().enumerate() {
            let pfx = if i == 0 { "    " } else { "    \\/ " };
            o.push_str(&format!("{pfx}{}_step\n", p.name));
        }
    }
    o.push_str("\nSpec == Init /\\ [][Next]_vars\n\n====\n");
    Ok((o, Some("INIT Init\nNEXT Next\n".into())))
}

fn parse_promela(content: &str, file: &Path) -> Result<PSpec> {
    let name = file.file_stem().and_then(|s| s.to_str()).unwrap_or("Imported").to_string();
    let (mut procs, mut chans, mut globals) = (Vec::new(), Vec::new(), Vec::new());
    let lines: Vec<&str> = content.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        if line.starts_with("proctype") || line.starts_with("active proctype") {
            let pname = extract_pname(line).unwrap_or_else(|| format!("P{}", procs.len()));
            let (mut body, mut depth) = (Vec::new(),
                line.matches('{').count() as i32 - line.matches('}').count() as i32);
            i += 1;
            while i < lines.len() && depth > 0 {
                depth += lines[i].matches('{').count() as i32 - lines[i].matches('}').count() as i32;
                if depth > 0 { body.push(lines[i].to_string()); }
                i += 1;
            }
            procs.push(PProc { name: pname, body }); continue;
        }
        if line.starts_with("chan ") { if let Some(c) = parse_chan(line) { chans.push(c); } }
        else if let Some(v) = parse_pvar(line) { globals.push(v); }
        i += 1;
    }
    Ok(PSpec { name, procs, chans, globals })
}

fn extract_pname(line: &str) -> Option<String> {
    let rest = line.split("proctype").nth(1)?.trim();
    let end = rest.find(|c: char| c == '(' || c.is_whitespace())?;
    let n = &rest[..end];
    if n.is_empty() { None } else { Some(n.into()) }
}

fn parse_chan(line: &str) -> Option<PChan> {
    let rest = line.strip_prefix("chan ")?.trim();
    let eq = rest.find('=')?;
    let name = rest[..eq].trim().to_string();
    let after = rest[eq + 1..].trim();
    let (cs, ce) = (after.find('[')?, after.find(']')?);
    let cap = after[cs + 1..ce].trim().parse().unwrap_or(1);
    let ts = after.find('{').map(|p| p + 1).unwrap_or(ce + 1);
    let te = after.find('}').unwrap_or(after.len());
    let mt = after.get(ts..te).map(|s| s.trim().into()).unwrap_or_else(|| "int".into());
    Some(PChan { name, capacity: cap, msg_type: mt })
}

fn parse_pvar(line: &str) -> Option<PVar> {
    let kw = ["byte", "int", "bool", "short", "bit", "unsigned"];
    let first = line.split_whitespace().next()?;
    if !kw.contains(&first) { return None; }
    let rest = line[first.len()..].trim().split("/*").next()?.split("//").next()?
        .trim_end_matches(';').trim();
    if rest.is_empty() { return None; }
    let (name, init) = if let Some(eq) = rest.find('=') {
        (rest[..eq].trim().into(), Some(rest[eq + 1..].trim().into()))
    } else { (rest.into(), None) };
    Some(PVar { name, type_name: first.into(), init })
}

struct ASpec { name: String, sigs: Vec<ASig>, preds: Vec<APred>, facts: Vec<AFact> }
struct ASig { name: String, is_abstract: bool, extends: Option<String>, fields: Vec<AField> }
struct AField { name: String, type_expr: String }
struct APred { name: String, params: Vec<String>, body: Vec<String> }
struct AFact { name: Option<String>, body: Vec<String> }

fn import_alloy(content: &str, file: &Path) -> Result<(String, Option<String>)> {
    let spec = parse_alloy(content, file)?;
    let mut o = String::new();
    o.push_str(&format!("---- MODULE {} ----\n", spec.name));
    o.push_str("EXTENDS Integers, Sequences, FiniteSets, TLC\n\n");
    let sig_names: Vec<&str> = spec.sigs.iter().map(|s| s.name.as_str()).collect();
    if !sig_names.is_empty() { o.push_str(&format!("CONSTANT {}\n", sig_names.join(", "))); }
    let fvars: Vec<String> = spec.sigs.iter()
        .flat_map(|s| s.fields.iter().map(|f| f.name.clone())).collect();
    if !fvars.is_empty() { o.push_str(&format!("\nVARIABLE {}\n", fvars.join(", "))); }
    for sig in &spec.sigs {
        if let Some(parent) = &sig.extends {
            o.push_str(&format!("\n{}_subset == {} \\subseteq {parent}\n", sig.name, sig.name));
        }
        for f in &sig.fields {
            let tt = alloy_type_tla(&f.type_expr, &sig_names);
            o.push_str(&format!("{}_type == {} \\in [{} -> {tt}]\n", f.name, f.name, sig.name));
        }
    }
    for pred in &spec.preds {
        let ps = if pred.params.is_empty() { String::new() }
                 else { format!("({})", pred.params.join(", ")) };
        o.push_str(&format!("\n{}{ps} ==\n    TRUE \\* TODO: translate Alloy body\n", pred.name));
    }
    for fact in &spec.facts {
        let label = fact.name.as_deref().unwrap_or("anonymous");
        o.push_str(&format!("\n\\* fact {label}\n"));
        for l in &fact.body {
            let t = l.trim();
            if !t.is_empty() { o.push_str(&format!("\\* {t}\n")); }
        }
    }
    o.push_str("\n====\n");
    Ok((o, None))
}

fn parse_alloy(content: &str, file: &Path) -> Result<ASpec> {
    let name = content.lines().find(|l| l.trim().starts_with("module"))
        .and_then(|l| l.trim().strip_prefix("module")?.trim().split_whitespace().next()
            .map(|s| s.rsplit('/').next().unwrap_or(s).into()))
        .unwrap_or_else(|| file.file_stem().and_then(|s| s.to_str())
            .unwrap_or("Imported").into());
    let (mut sigs, mut preds, mut facts) = (Vec::new(), Vec::new(), Vec::new());
    let lines: Vec<&str> = content.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        if line.contains("sig ") && !line.starts_with("//") && !line.starts_with("--") {
            if let Some(s) = parse_asig(line, &lines, &mut i) { sigs.push(s); continue; }
        }
        if line.starts_with("pred ") {
            let (pn, pp) = parse_apred_header(line);
            if let Some(b) = collect_block(line, &lines, &mut i) {
                preds.push(APred { name: pn, params: pp, body: b }); continue;
            }
        }
        if line.starts_with("fact") {
            let fn_ = line.strip_prefix("fact").and_then(|r| {
                let r = r.trim();
                let e = r.find(|c: char| c == '{' || c.is_whitespace())?;
                let n = r[..e].trim();
                if n.is_empty() { None } else { Some(n.into()) }
            });
            if let Some(b) = collect_block(line, &lines, &mut i) {
                facts.push(AFact { name: fn_, body: b }); continue;
            }
        }
        i += 1;
    }
    Ok(ASpec { name, sigs, preds, facts })
}

fn parse_asig(line: &str, lines: &[&str], idx: &mut usize) -> Option<ASig> {
    let after = line.split("sig ").nth(1)?;
    let ne = after.find(|c: char| c == '{' || c.is_whitespace())?;
    let name = after[..ne].trim().to_string();
    let extends = after.find("extends").map(|p| after[p + 7..].trim()
        .split(|c: char| c == '{' || c == ',' || c.is_whitespace()).next().unwrap_or("").into()
    ).filter(|s: &String| !s.is_empty());
    let mut fields = Vec::new();
    let mut depth = line.matches('{').count() as i32 - line.matches('}').count() as i32;
    if let Some(bs) = line.find('{') {
        parse_afields(&line[bs + 1..line.find('}').unwrap_or(line.len())], &mut fields);
    }
    *idx += 1;
    while *idx < lines.len() && depth > 0 {
        depth += lines[*idx].matches('{').count() as i32 - lines[*idx].matches('}').count() as i32;
        if depth > 0 { parse_afields(lines[*idx], &mut fields); }
        *idx += 1;
    }
    Some(ASig { name, is_abstract: line.contains("abstract"), extends, fields })
}

fn parse_afields(line: &str, fields: &mut Vec<AField>) {
    let t = line.trim();
    if t.is_empty() || t.starts_with("//") || t.starts_with("--") { return; }
    for part in t.split(',') {
        let part = part.trim().trim_end_matches(',');
        if let Some(cp) = part.find(':') {
            let n = part[..cp].trim(); let ty = part[cp + 1..].trim();
            if !n.is_empty() && !ty.is_empty() {
                fields.push(AField { name: n.into(), type_expr: ty.into() });
            }
        }
    }
}

fn collect_block(first: &str, lines: &[&str], idx: &mut usize) -> Option<Vec<String>> {
    let mut depth = first.matches('{').count() as i32 - first.matches('}').count() as i32;
    if depth <= 0 { *idx += 1; return Some(Vec::new()); }
    let mut body = Vec::new();
    *idx += 1;
    while *idx < lines.len() && depth > 0 {
        depth += lines[*idx].matches('{').count() as i32 - lines[*idx].matches('}').count() as i32;
        if depth > 0 { body.push(lines[*idx].to_string()); }
        *idx += 1;
    }
    Some(body)
}

fn parse_apred_header(line: &str) -> (String, Vec<String>) {
    let rest = line.strip_prefix("pred ").unwrap_or(line).trim();
    let ne = rest.find(|c: char| c == '[' || c == '(' || c == '{' || c.is_whitespace())
        .unwrap_or(rest.len());
    let mut params = Vec::new();
    if let (Some(bs), Some(be)) = (rest.find('['), rest.find(']')) {
        for p in rest[bs + 1..be].split(',') {
            let pn = p.trim().split(':').next().unwrap_or("").trim().to_string();
            if !pn.is_empty() { params.push(pn); }
        }
    }
    (rest[..ne].trim().into(), params)
}

fn alloy_type_tla(atype: &str, sigs: &[&str]) -> String {
    let core = atype.trim()
        .strip_prefix("set ").or_else(|| atype.trim().strip_prefix("lone "))
        .or_else(|| atype.trim().strip_prefix("one "))
        .or_else(|| atype.trim().strip_prefix("some "))
        .unwrap_or(atype.trim());
    if sigs.contains(&core) { return core.into(); }
    match core {
        "Int" => "Int".into(), "String" => "STRING".into(),
        "Bool" => "BOOLEAN".into(), _ => core.into(),
    }
}

fn write_output(path: Option<&Path>, data: &[u8]) -> Result<()> {
    match path {
        Some(p) => {
            std::fs::write(p, data).with_context(|| format!("Failed to write {}", p.display()))?;
            eprintln!("Wrote output to {}", p.display());
        }
        None => { std::io::stdout().lock().write_all(data).context("Failed to write to stdout")?; }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_sm_basic_import() {
        let json = r#"{"name":"TrafficLight","variables":{"light":"string","count":"integer"},
            "init":{"light":"red","count":0},"transitions":[
            {"name":"GoGreen","guard":"light = \"red\"","effect":{"light":"\"green\""}},
            {"name":"GoRed","guard":"light = \"yellow\"","effect":{"light":"\"red\"","count":"count + 1"}}],
            "invariants":["light \\in {\"red\",\"green\",\"yellow\"}"]}"#;
        let (tla, cfg) = import_json_sm(json, Path::new("T.json")).expect("parse");
        assert!(tla.contains("MODULE TrafficLight"));
        assert!(tla.contains("VARIABLE count, light"));
        assert!(tla.contains("Init ==") && tla.contains("GoGreen =="));
        assert!(tla.contains("Spec == Init /\\ [][Next]_vars"));
        assert!(tla.contains("Inv1 ==") && tla.contains("TypeOK =="));
        assert!(tla.contains("===="));
        let cfg = cfg.unwrap();
        assert!(cfg.contains("INIT Init") && cfg.contains("INVARIANT TypeOK"));
    }

    #[test]
    fn test_json_sm_empty_vars_rejected() {
        let json = r#"{"name":"E","variables":{},"init":{},"transitions":[],"invariants":[]}"#;
        assert!(import_json_sm(json, Path::new("e.json")).is_err());
    }

    #[test]
    fn test_json_val_primitives() {
        assert_eq!(json_val_to_tla(&serde_json::json!(42)), "42");
        assert_eq!(json_val_to_tla(&serde_json::json!(true)), "TRUE");
        assert_eq!(json_val_to_tla(&serde_json::json!("hi")), "\"hi\"");
        assert_eq!(json_val_to_tla(&serde_json::json!([1, 2])), "<<1, 2>>");
    }

    #[test]
    fn test_effect_val_string_passthrough() {
        assert_eq!(effect_val(&serde_json::json!("x + 1")), "x + 1");
        assert_eq!(effect_val(&serde_json::json!(5)), "5");
    }

    #[test]
    fn test_type_constraints() {
        assert_eq!(type_constraint("x", "integer"), Some("x \\in Int".into()));
        assert_eq!(type_constraint("y", "boolean"), Some("y \\in BOOLEAN".into()));
        assert_eq!(type_constraint("z", "unknown"), None);
    }

    #[test]
    fn test_unchanged_vars() {
        let json = r#"{"name":"C","variables":{"a":"int","b":"int"},
            "init":{"a":0,"b":0},"transitions":[
            {"name":"IncA","guard":"TRUE","effect":{"a":"a+1"}}],"invariants":[]}"#;
        let (tla, _) = import_json_sm(json, Path::new("c.json")).unwrap();
        assert!(tla.contains("UNCHANGED b"));
    }

    #[test]
    fn test_promela_parse() {
        let src = "int x = 0;\nchan ch = [2] of { int };\nproctype P() {\n  x = 1;\n}\n";
        let (tla, _) = import_promela(src, Path::new("t.pml")).unwrap();
        assert!(tla.contains("MODULE t") && tla.contains("VARIABLE x, ch, pc_P"));
        assert!(tla.contains("P_step ==") && tla.contains("===="));
    }

    #[test]
    fn test_promela_empty() {
        let (tla, _) = import_promela("", Path::new("e.pml")).unwrap();
        assert!(tla.contains("UNCHANGED vars"));
    }

    #[test]
    fn test_promela_helpers() {
        assert_eq!(extract_pname("proctype Foo() {"), Some("Foo".into()));
        assert_eq!(extract_pname("active proctype Bar() {"), Some("Bar".into()));
        let ch = parse_chan("chan c = [3] of { int }").unwrap();
        assert_eq!(ch.name, "c"); assert_eq!(ch.capacity, 3);
        let v = parse_pvar("int x = 5;").unwrap();
        assert_eq!(v.name, "x"); assert_eq!(v.init, Some("5".into()));
        assert!(parse_pvar("proctype X() {").is_none());
    }

    #[test]
    fn test_alloy_parse() {
        let src = "module ex\nsig A {}\nsig B extends A { f: Int }\npred p[x: A] {\n  x in B\n}\nfact F { all a: A | a in B }\n";
        let (tla, cfg) = import_alloy(src, Path::new("ex.als")).unwrap();
        assert!(tla.contains("MODULE ex") && tla.contains("CONSTANT A, B"));
        assert!(tla.contains("VARIABLE f") && tla.contains("B_subset == B \\subseteq A"));
        assert!(tla.contains("p(x) ==") && tla.contains("fact F") && tla.contains("===="));
        assert!(cfg.is_none());
    }

    #[test]
    fn test_alloy_type_mapping() {
        let sigs = vec!["Node"];
        assert_eq!(alloy_type_tla("Int", &sigs), "Int");
        assert_eq!(alloy_type_tla("set Node", &sigs), "Node");
        assert_eq!(alloy_type_tla("Bool", &sigs), "BOOLEAN");
    }

    #[test]
    fn test_alloy_module_name_fallback() {
        let spec = parse_alloy("sig A {}\n", Path::new("fb.als")).unwrap();
        assert_eq!(spec.name, "fb");
    }

    #[test]
    fn test_import_format_enum_distinct() {
        assert_ne!(ImportFormat::JsonStateMachine, ImportFormat::Promela);
        assert_ne!(ImportFormat::Promela, ImportFormat::Alloy);
    }
}
