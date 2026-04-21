// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::json_output::JsonValue;
use crate::EvalCtx;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use tla_core::ast::{Expr, ModuleTarget, Unit};
use tla_core::{lower, parse, pretty_expr, FileId, SyntaxNode};

#[derive(Debug, thiserror::Error)]
pub enum TraceActionLabelMappingError {
    #[error("failed to read mapping config: {path}: {source}")]
    ReadConfig {
        path: String,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to parse mapping config TOML: {path}: {source}")]
    ParseToml {
        path: String,
        #[source]
        source: toml::de::Error,
    },
    #[error("duplicate action label in mapping config: {label}")]
    DuplicateLabel { label: String },
    #[error("action label {label} has duplicate param name: {param}")]
    DuplicateParamName { label: String, param: String },
    #[error(
        "mapping config module mismatch: config spec.module={config:?}, loaded module {loaded:?}"
    )]
    ModuleMismatch { config: String, loaded: String },
    #[error("invalid operator reference for action label {label}: {operator:?}: {reason}")]
    InvalidOperatorRef {
        label: String,
        operator: String,
        reason: String,
    },
    #[error("unknown operator reference for action label {label}: {operator:?}")]
    UnknownOperator { label: String, operator: String },
    #[error(
        "operator arity mismatch for action label {label}: {operator:?}: expected {expected}, got {got}"
    )]
    OperatorArityMismatch {
        label: String,
        operator: String,
        expected: usize,
        got: usize,
    },
    #[error(
        "operator param name mismatch for action label {label}: {operator:?}: expected {expected:?}, got {got:?}"
    )]
    OperatorParamNameMismatch {
        label: String,
        operator: String,
        expected: Vec<String>,
        got: Vec<String>,
    },
    #[error(
        "unsupported higher-order operator for action label {label}: {operator:?}: param {param:?} has arity {arity}"
    )]
    UnsupportedHigherOrderOperator {
        label: String,
        operator: String,
        param: String,
        arity: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
pub enum ActionParamEncoding {
    #[serde(rename = "tla-json")]
    TlaJson,
}

fn default_param_encoding() -> ActionParamEncoding {
    ActionParamEncoding::TlaJson
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperatorRef {
    Unqualified { name: String },
    ModuleRef { target: String, name: String },
}

impl OperatorRef {
    fn parse_config_operator(
        label: &str,
        operator: &str,
    ) -> Result<Self, TraceActionLabelMappingError> {
        let src =
            format!("---- MODULE __TLA2_ActionLabelMappingCfg__ ----\nTmp == {operator}\n====\n");

        let parse_result = parse(&src);
        if let Some(err) = parse_result.errors.first() {
            return Err(TraceActionLabelMappingError::InvalidOperatorRef {
                label: label.to_string(),
                operator: operator.to_string(),
                reason: format!("parse error: {}", err.message),
            });
        }

        let tree = SyntaxNode::new_root(parse_result.green_node);
        let lowered = lower(FileId(0), &tree);
        if let Some(err) = lowered.errors.first() {
            return Err(TraceActionLabelMappingError::InvalidOperatorRef {
                label: label.to_string(),
                operator: operator.to_string(),
                reason: format!("lowering error: {}", err.message),
            });
        }

        let module =
            lowered
                .module
                .ok_or_else(|| TraceActionLabelMappingError::InvalidOperatorRef {
                    label: label.to_string(),
                    operator: operator.to_string(),
                    reason: "failed to parse operator: no module produced".to_string(),
                })?;

        let tmp_def = module.units.iter().find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "Tmp" => Some(def),
            _ => None,
        });
        let Some(tmp_def) = tmp_def else {
            return Err(TraceActionLabelMappingError::InvalidOperatorRef {
                label: label.to_string(),
                operator: operator.to_string(),
                reason: "failed to parse operator: missing Tmp definition".to_string(),
            });
        };

        match &tmp_def.body.node {
            Expr::Ident(name, _) => Ok(OperatorRef::Unqualified { name: name.clone() }),
            Expr::ModuleRef(target, name, args) => {
                if !args.is_empty() {
                    return Err(TraceActionLabelMappingError::InvalidOperatorRef {
                        label: label.to_string(),
                        operator: operator.to_string(),
                        reason: "operator must be a reference (no args): expected `Op` or `M!Op`"
                            .to_string(),
                    });
                }
                match target {
                    ModuleTarget::Named(t) => Ok(OperatorRef::ModuleRef {
                        target: t.clone(),
                        name: name.clone(),
                    }),
                    ModuleTarget::Parameterized(_, _) | ModuleTarget::Chained(_) => {
                        Err(TraceActionLabelMappingError::InvalidOperatorRef {
                            label: label.to_string(),
                            operator: operator.to_string(),
                            reason: "operator must be a simple reference: expected `Op` or `M!Op`"
                                .to_string(),
                        })
                    }
                }
            }
            other => Err(TraceActionLabelMappingError::InvalidOperatorRef {
                label: label.to_string(),
                operator: operator.to_string(),
                reason: format!(
                    "operator must be a reference like `Op` or `M!Op`, got: {}",
                    pretty_expr(other)
                ),
            }),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ActionLabelMapping {
    pub label: String,
    pub operator_raw: String,
    pub operator: OperatorRef,
    pub params: Vec<String>,
    pub param_encoding: ActionParamEncoding,
    pub allow_stutter: bool,
}

#[derive(Debug, Clone)]
pub struct ActionLabelMappingConfig {
    pub spec_module: Option<String>,
    by_label: HashMap<String, ActionLabelMapping>,
}

impl ActionLabelMappingConfig {
    pub fn from_path(path: &Path) -> Result<Self, TraceActionLabelMappingError> {
        let toml_str = std::fs::read_to_string(path).map_err(|source| {
            TraceActionLabelMappingError::ReadConfig {
                path: path.display().to_string(),
                source,
            }
        })?;
        Self::from_toml_str(path.display().to_string(), &toml_str)
    }

    /// Load a mapping config from a path and validate it for the given loaded spec module.
    ///
    /// This is intended to be called once, when a mapping config is first applied to a trace
    /// validator / runtime checker.
    pub fn from_path_for_spec(
        path: &Path,
        loaded_module_name: &str,
        ctx: &EvalCtx,
    ) -> Result<Self, TraceActionLabelMappingError> {
        let cfg = Self::from_path(path)?;
        cfg.validate_for_spec(loaded_module_name, ctx)?;
        Ok(cfg)
    }

    pub fn from_toml_str(
        path_display: String,
        toml_str: &str,
    ) -> Result<Self, TraceActionLabelMappingError> {
        let cfg: TomlConfig =
            toml::from_str(toml_str).map_err(|source| TraceActionLabelMappingError::ParseToml {
                path: path_display,
                source,
            })?;
        cfg.try_into_config()
    }

    /// Parse a mapping config and validate it for the given loaded spec module.
    ///
    /// This is intended to be called once, when a mapping config is first applied to a trace
    /// validator / runtime checker.
    pub fn from_toml_str_for_spec(
        path_display: String,
        toml_str: &str,
        loaded_module_name: &str,
        ctx: &EvalCtx,
    ) -> Result<Self, TraceActionLabelMappingError> {
        let cfg = Self::from_toml_str(path_display, toml_str)?;
        cfg.validate_for_spec(loaded_module_name, ctx)?;
        Ok(cfg)
    }

    pub fn mapping(&self, label: &str) -> Option<&ActionLabelMapping> {
        self.by_label.get(label)
    }

    pub fn validate_for_spec(
        &self,
        loaded_module_name: &str,
        ctx: &EvalCtx,
    ) -> Result<(), TraceActionLabelMappingError> {
        if let Some(config_module) = &self.spec_module {
            if config_module != loaded_module_name {
                return Err(TraceActionLabelMappingError::ModuleMismatch {
                    config: config_module.clone(),
                    loaded: loaded_module_name.to_string(),
                });
            }
        }

        for mapping in self.by_label.values() {
            let def = match &mapping.operator {
                OperatorRef::Unqualified { name } => ctx.get_op(name).ok_or_else(|| {
                    TraceActionLabelMappingError::UnknownOperator {
                        label: mapping.label.clone(),
                        operator: mapping.operator_raw.clone(),
                    }
                })?,
                OperatorRef::ModuleRef { target, name } => {
                    let module_name = if let Some(info) = ctx.get_instance(target) {
                        info.module_name.clone()
                    } else if let Some(def) = ctx.get_op(target) {
                        match &def.body.node {
                            Expr::InstanceExpr(module_name, _) => module_name.clone(),
                            _ => {
                                return Err(TraceActionLabelMappingError::UnknownOperator {
                                    label: mapping.label.clone(),
                                    operator: mapping.operator_raw.clone(),
                                });
                            }
                        }
                    } else {
                        return Err(TraceActionLabelMappingError::UnknownOperator {
                            label: mapping.label.clone(),
                            operator: mapping.operator_raw.clone(),
                        });
                    };

                    ctx.get_instance_op(&module_name, name).ok_or_else(|| {
                        TraceActionLabelMappingError::UnknownOperator {
                            label: mapping.label.clone(),
                            operator: mapping.operator_raw.clone(),
                        }
                    })?
                }
            };

            let expected = def.params.len();
            let got = mapping.params.len();
            if expected != got {
                return Err(TraceActionLabelMappingError::OperatorArityMismatch {
                    label: mapping.label.clone(),
                    operator: mapping.operator_raw.clone(),
                    expected,
                    got,
                });
            }

            if let Some(param) = def.params.iter().find(|p| p.arity > 0) {
                return Err(
                    TraceActionLabelMappingError::UnsupportedHigherOrderOperator {
                        label: mapping.label.clone(),
                        operator: mapping.operator_raw.clone(),
                        param: param.name.node.clone(),
                        arity: param.arity,
                    },
                );
            }

            let expected_names: Vec<String> =
                def.params.iter().map(|p| p.name.node.clone()).collect();
            if expected_names != mapping.params {
                return Err(TraceActionLabelMappingError::OperatorParamNameMismatch {
                    label: mapping.label.clone(),
                    operator: mapping.operator_raw.clone(),
                    expected: expected_names,
                    got: mapping.params.clone(),
                });
            }
        }

        Ok(())
    }

    /// Bind trace-provided params for a label into the operator's formal order.
    ///
    /// v1 semantics:
    /// - The mapping config provides an explicit `params = ["p1", ..., "pk"]` list.
    /// - The trace must provide exactly the same set of param keys.
    /// - Params are returned in the `params` list order.
    pub fn bind_params(
        &self,
        label: &str,
        params: &HashMap<String, JsonValue>,
    ) -> Result<Vec<(String, JsonValue)>, ActionLabelInstanceError> {
        let mapping =
            self.by_label
                .get(label)
                .ok_or_else(|| ActionLabelInstanceError::UnknownLabel {
                    label: label.to_string(),
                })?;

        let expected: HashSet<&str> = mapping
            .params
            .iter()
            .map(std::string::String::as_str)
            .collect();
        let got: HashSet<&str> = params.keys().map(std::string::String::as_str).collect();
        if expected != got {
            let mut expected_vec: Vec<String> = mapping.params.clone();
            let mut got_vec: Vec<String> = params.keys().cloned().collect();
            expected_vec.sort();
            got_vec.sort();
            return Err(ActionLabelInstanceError::ParamMismatch {
                label: mapping.label.clone(),
                expected: expected_vec,
                got: got_vec,
            });
        }

        mapping
            .params
            .iter()
            .map(|p| {
                let v = params
                    .get(p)
                    .ok_or_else(|| ActionLabelInstanceError::ParamMismatch {
                        label: mapping.label.clone(),
                        expected: mapping.params.clone(),
                        got: params.keys().cloned().collect(),
                    })?;
                Ok((p.clone(), v.clone()))
            })
            .collect()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ActionLabelInstanceError {
    #[error("unknown action label: {label}")]
    UnknownLabel { label: String },
    #[error("action label {label} params mismatch: expected {expected:?}, got {got:?}")]
    ParamMismatch {
        label: String,
        expected: Vec<String>,
        got: Vec<String>,
    },
}

#[derive(Debug, Default, Deserialize)]
struct TomlSpec {
    #[serde(default)]
    module: Option<String>,
}

#[derive(Debug, Deserialize)]
struct TomlActionMapping {
    label: String,
    operator: String,
    #[serde(default)]
    params: Vec<String>,
    #[serde(default = "default_param_encoding")]
    param_encoding: ActionParamEncoding,
    #[serde(default)]
    allow_stutter: bool,
}

#[derive(Debug, Default, Deserialize)]
struct TomlConfig {
    #[serde(default)]
    spec: TomlSpec,
    #[serde(default)]
    actions: Vec<TomlActionMapping>,
}

impl TomlConfig {
    fn try_into_config(self) -> Result<ActionLabelMappingConfig, TraceActionLabelMappingError> {
        let mut by_label = HashMap::new();
        for action in self.actions {
            if by_label.contains_key(&action.label) {
                return Err(TraceActionLabelMappingError::DuplicateLabel {
                    label: action.label,
                });
            }

            let mut seen = HashSet::with_capacity(action.params.len());
            for p in &action.params {
                if !seen.insert(p) {
                    return Err(TraceActionLabelMappingError::DuplicateParamName {
                        label: action.label.clone(),
                        param: p.clone(),
                    });
                }
            }

            let operator_ref = OperatorRef::parse_config_operator(&action.label, &action.operator)?;
            by_label.insert(
                action.label.clone(),
                ActionLabelMapping {
                    label: action.label,
                    operator_raw: action.operator,
                    operator: operator_ref,
                    params: action.params,
                    param_encoding: action.param_encoding,
                    allow_stutter: action.allow_stutter,
                },
            );
        }

        Ok(ActionLabelMappingConfig {
            spec_module: self.spec.module,
            by_label,
        })
    }
}
