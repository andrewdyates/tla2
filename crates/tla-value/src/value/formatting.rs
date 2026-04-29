// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::Value;
use std::fmt;

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", if *b { "TRUE" } else { "FALSE" }),
            Value::SmallInt(n) => write!(f, "{n}"),
            Value::Int(n) => write!(f, "{n}"),
            Value::String(s) => write!(f, "{s:?}"),
            Value::ModelValue(s) => write!(f, "@{s}"),
            Value::Set(s) => {
                write!(f, "{{")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v:?}")?;
                }
                write!(f, "}}")
            }
            Value::Interval(iv) => {
                // Display as interval notation for debugging
                write!(f, "{}..{}", iv.low, iv.high)
            }
            Value::Subset(sv) => {
                // Display as SUBSET base notation
                write!(f, "SUBSET {:?}", sv.base)
            }
            Value::FuncSet(fsv) => {
                // Display as function set notation
                write!(f, "[{:?} -> {:?}]", fsv.domain, fsv.codomain)
            }
            Value::RecordSet(rsv) => {
                // Display as record set notation
                write!(f, "[")?;
                for (i, (k, v)) in rsv.fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}: {v:?}")?;
                }
                write!(f, "]")
            }
            Value::TupleSet(tsv) => {
                // Display as tuple set notation (cartesian product)
                if tsv.components.is_empty() {
                    write!(f, "{{<<>>}}")
                } else {
                    for (i, c) in tsv.components.iter().enumerate() {
                        if i > 0 {
                            write!(f, " \\X ")?;
                        }
                        write!(f, "{c:?}")?;
                    }
                    Ok(())
                }
            }
            Value::SetCup(scv) => {
                // Display as union notation
                write!(f, "({:?} \\cup {:?})", scv.set1, scv.set2)
            }
            Value::SetCap(scv) => {
                // Display as intersection notation
                write!(f, "({:?} \\cap {:?})", scv.set1, scv.set2)
            }
            Value::SetDiff(sdv) => {
                // Display as set difference notation
                write!(f, "({:?} \\ {:?})", sdv.set1, sdv.set2)
            }
            Value::SetPred(spv) => {
                // Display as set filter notation
                write!(f, "{{x \\in {:?} : <pred#{}>}}", spv.source(), spv.id())
            }
            Value::KSubset(ksv) => {
                // Display as Ksubsets notation
                write!(f, "Ksubsets({:?}, {})", ksv.base, ksv.k)
            }
            Value::BigUnion(uv) => {
                // Display as UNION notation
                write!(f, "UNION {:?}", uv.set)
            }
            Value::Seq(s) => {
                write!(f, "<<")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v:?}")?;
                }
                write!(f, ">>")
            }
            Value::Tuple(t) => {
                write!(f, "<<")?;
                for (i, v) in t.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v:?}")?;
                }
                write!(f, ">>")
            }
            Value::Record(r) => {
                write!(f, "[")?;
                for (i, (k, v)) in r.iter_str().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k} |-> {v:?}")?;
                }
                write!(f, "]")
            }
            Value::Func(func) => {
                write!(f, "[")?;
                for (i, (k, v)) in func.mapping_iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k:?} |-> {v:?}")?;
                }
                write!(f, "]")
            }
            Value::IntFunc(func) => {
                write!(f, "[")?;
                for (i, v) in func.values.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} |-> {:?}", func.min + i as i64, v)?;
                }
                write!(f, "]")
            }
            Value::LazyFunc(func) => match func.name() {
                Some(name) => write!(f, "<lazy-func:{}#{}>", name, func.id()),
                None => write!(f, "<lazy-func#{}>", func.id()),
            },
            Value::Closure(c) => {
                write!(f, "LAMBDA ")?;
                for (i, p) in c.params().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, " : <body#{}>", c.id())
            }
            Value::StringSet => write!(f, "STRING"),
            Value::AnySet => write!(f, "ANY"),
            Value::SeqSet(ssv) => write!(f, "Seq({:?})", ssv.base),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}
