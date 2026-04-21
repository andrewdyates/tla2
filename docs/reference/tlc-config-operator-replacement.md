# TLC Config Operator Replacement (`<-`) Mechanism

**Date:** 2026-01-19
**Re:** #338, #339
**Status:** Reference Documentation

## Overview

TLC's config file supports operator replacement via the `<-` syntax. This document explains how TLC handles this mechanism, based on baseline source analysis.

## Config File Syntax

```
CONSTANT
  Acceptor <- MCAcceptor
```

This replaces every reference to `Acceptor` with `MCAcceptor`.

## TLC Implementation

### Config Parsing

**Citation:** `~/tlaplus/tlatools/.../tlc2/tool/impl/ModelConfig.java:338-380`

When parsing `A <- B`:
```java
if (tt.image.equals("<-")) {
    tt = getNextToken(tmgr, buf);
    // ...
    final String string = (String)line.elementAt(0);  // "A"
    this.overrides.put(string, tt.image);              // "A" -> "B"
    this.overridesReverseMap.put(tt.image, string);    // "B" -> "A"
}
```

The `overrides` hash table stores: `{lhs: rhs}` where lhs is the original name and rhs is the replacement.

### Applying Overrides

**Citation:** `~/tlaplus/tlatools/.../tlc2/tool/impl/SpecProcessor.java:785-877`

TLC applies overrides in two phases:

**Phase 1: Constants** (lines 785-805)
```java
for (int i = 0; i < rootConsts.length; i++) {
    UniqueString lhs = rootConsts[i].getName();
    String rhs = (String) overrides.get(lhs.toString());
    if (rhs != null) {
        Object myVal = this.defns.get(rhs);  // Look up replacement definition
        rootConsts[i].setToolObject(toolId, myVal);
        this.defns.put(lhs, myVal);
    }
}
```

**Phase 2: Operator Definitions** (lines 818-877)
```java
for (int i = 0; i < rootOpDefs.length; i++) {
    UniqueString lhs = rootOpDefs[i].getName();
    String rhs = (String) overrides.get(lhs.toString());
    if (rhs != null) {
        Object myVal = this.defns.get(rhs);  // Look up replacement definition
        rootOpDefs[i].setToolObject(toolId, myVal);
        this.defns.put(lhs, myVal);
    }
}
```

### Key Insight

The replacement name (e.g., `const_156180051387243000`) is just a regular operator defined in the TLA+ module. TLC doesn't have special handling for Toolbox-generated names - it simply looks up the operator definition in `defns`.

## Toolbox-Generated Format

The TLA+ Toolbox generates configs like:
```
CONSTANT
  a1 = a1
  Acceptor <- const_156180051387243000
```

With corresponding TLA+ definitions:
```tla
CONSTANTS a1, a2, a3

const_156180051387243000 == {a1, a2, a3}
```

### `a1 = a1` Pattern

This declares `a1` as a **model value** - a special value that equals only itself. Model values are used for symmetry sets and abstract constants.

**Citation:** `~/tlaplus/tlatools/.../tlc2/tool/impl/ModelConfig.java:420-437`

When `id = value` is parsed, TLC creates a concrete value and stores it in the constants table:
```java
line.addElement(this.parseValue(tt, scs, tmgr, buf));
constants.addElement(line);
```

## TLA2 Implementation Notes

### Fixed Issues

1. **MCVoting** (#337): Basic `<-` operator replacement not working in `expand_operators`
2. **MCVoting_2** (#338): Named INSTANCE causing Init namespace pollution

### Remaining Issues

Specs using Toolbox format with unconstrained Init (MCPaxos, EWD840_json, etc.) still fail because TLA2's constraint extraction doesn't handle function constructor Init patterns.

See: reports/research/2026-01-19-mcvoting2-constraint-extraction.md

## Verification Commands

```bash
# MCVoting (Paxos/) - works
cargo run --release --bin tla2 -- check \
  ~/tlaplus-examples/specifications/Paxos/MCVoting.tla \
  --config ~/tlaplus-examples/specifications/Paxos/MCVoting.cfg

# MCVoting_2 (PaxosHowToWinATuringAward/) - works (6752 states)
cargo run --release --bin tla2 -- check \
  ~/tlaplus-examples/specifications/PaxosHowToWinATuringAward/MCVoting.tla \
  --config ~/tlaplus-examples/specifications/PaxosHowToWinATuringAward/MCVoting.cfg
```

## Citations

- `~/tlaplus/tlatools/.../tlc2/tool/impl/ModelConfig.java:338-380` - Config parsing for `<-`
- `~/tlaplus/tlatools/.../tlc2/tool/impl/SpecProcessor.java:785-877` - Override application
- `~/tlaplus/tlatools/.../tlc2/value/impl/ModelValue.java` - Model value implementation

## Lineage

- Original research: Researcher session 2026-01-19
- Built on: TLC source analysis, #338/#339 investigation
