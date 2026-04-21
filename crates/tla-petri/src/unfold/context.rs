// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort/value algebra and shared lookup context for colored-net unfolding.

use std::collections::HashMap;

use crate::error::PnmlError;
use crate::hlpnml::{ColorSort, ColorTerm, ColoredNet};

use super::ColorValue;

/// Lookup context for sort definitions and variable-to-sort mappings.
pub(super) struct UnfoldContext {
    /// Sort id → sort definition.
    pub(super) sorts: HashMap<String, ColorSort>,
    /// Variable id → sort id.
    pub(super) var_sorts: HashMap<String, String>,
}

impl UnfoldContext {
    pub(super) fn new(colored: &ColoredNet) -> Result<Self, PnmlError> {
        let mut sorts = HashMap::new();
        for sort in &colored.sorts {
            sorts.insert(sort.id().to_string(), sort.clone());
        }

        let mut var_sorts = HashMap::new();
        for var in &colored.variables {
            var_sorts.insert(var.id.clone(), var.sort_id.clone());
        }

        Ok(UnfoldContext { sorts, var_sorts })
    }

    /// Get the sort for a colored place.
    pub(super) fn sort_for_place(
        &self,
        place: &crate::hlpnml::ColoredPlace,
    ) -> Result<&ColorSort, PnmlError> {
        self.sorts.get(&place.sort_id).ok_or_else(|| {
            PnmlError::MissingElement(format!("sort '{}' for place '{}'", place.sort_id, place.id))
        })
    }

    /// Get the sort for a variable.
    pub(super) fn sort_for_variable(&self, var_id: &str) -> Result<&ColorSort, PnmlError> {
        let sort_id = self.var_sorts.get(var_id).ok_or_else(|| {
            PnmlError::MissingElement(format!("variable '{var_id}' not declared"))
        })?;
        self.sorts.get(sort_id).ok_or_else(|| {
            PnmlError::MissingElement(format!("sort '{sort_id}' for variable '{var_id}'"))
        })
    }

    /// Compute cardinality of a sort.
    pub(super) fn sort_cardinality(&self, sort: &ColorSort) -> Result<usize, PnmlError> {
        match sort {
            ColorSort::Dot { .. } => Ok(1),
            ColorSort::CyclicEnum { constants, .. } => Ok(constants.len()),
            ColorSort::Product { components, .. } => {
                let mut cardinality = 1usize;
                for component_id in components {
                    let component_sort = self.sorts.get(component_id).ok_or_else(|| {
                        PnmlError::MissingElement(format!(
                            "component sort '{component_id}' for product sort '{}'",
                            sort.name()
                        ))
                    })?;
                    cardinality = cardinality
                        .checked_mul(self.sort_cardinality(component_sort)?)
                        .ok_or_else(|| PnmlError::UnsupportedNetType {
                            net_type: format!(
                                "product sort '{}' cardinality overflow",
                                sort.name()
                            ),
                        })?;
                }
                Ok(cardinality)
            }
        }
    }

    pub(super) fn sort_value_names(&self, sort: &ColorSort) -> Result<Vec<String>, PnmlError> {
        let cardinality = self.sort_cardinality(sort)?;
        (0..cardinality)
            .map(|value| self.sort_value_name(sort, value))
            .collect()
    }

    pub(super) fn sort_value_name(
        &self,
        sort: &ColorSort,
        value: ColorValue,
    ) -> Result<String, PnmlError> {
        match sort {
            ColorSort::Dot { .. } => Ok("dot".to_string()),
            ColorSort::CyclicEnum { constants, .. } => constants
                .get(value)
                .map(|constant| constant.name.clone())
                .ok_or_else(|| {
                    PnmlError::InvalidMarking(format!(
                        "color value {value} out of range for sort '{}'",
                        sort.name()
                    ))
                }),
            ColorSort::Product { components, .. } => {
                let component_values = self.unflatten_product_value(components, value)?;
                let mut names = Vec::with_capacity(components.len());
                for (component_id, component_value) in components.iter().zip(component_values) {
                    let component_sort = self.sorts.get(component_id).ok_or_else(|| {
                        PnmlError::MissingElement(format!(
                            "component sort '{component_id}' for product sort '{}'",
                            sort.name()
                        ))
                    })?;
                    names.push(self.sort_value_name(component_sort, component_value)?);
                }
                Ok(names.join("_"))
            }
        }
    }

    pub(super) fn flatten_product_value(
        &self,
        component_sort_ids: &[String],
        component_values: &[ColorValue],
    ) -> Result<ColorValue, PnmlError> {
        if component_sort_ids.len() != component_values.len() {
            return Err(PnmlError::InvalidMarking(format!(
                "tuple arity {} does not match product sort arity {}",
                component_values.len(),
                component_sort_ids.len()
            )));
        }

        let mut value = 0usize;
        for (component_sort_id, component_value) in component_sort_ids.iter().zip(component_values)
        {
            let component_sort = self.sorts.get(component_sort_id).ok_or_else(|| {
                PnmlError::MissingElement(format!(
                    "component sort '{component_sort_id}' for product value"
                ))
            })?;
            let radix = self.sort_cardinality(component_sort)?;
            if *component_value >= radix {
                return Err(PnmlError::InvalidMarking(format!(
                    "component value {} out of range for sort '{component_sort_id}'",
                    component_value
                )));
            }
            value = value
                .checked_mul(radix)
                .and_then(|prefix| prefix.checked_add(*component_value))
                .ok_or_else(|| PnmlError::UnsupportedNetType {
                    net_type: format!("product sort '{}' flattening overflow", component_sort_id),
                })?;
        }
        Ok(value)
    }

    pub(super) fn unflatten_product_value(
        &self,
        component_sort_ids: &[String],
        value: ColorValue,
    ) -> Result<Vec<ColorValue>, PnmlError> {
        let mut radices = Vec::with_capacity(component_sort_ids.len());
        let mut total = 1usize;
        for component_sort_id in component_sort_ids {
            let component_sort = self.sorts.get(component_sort_id).ok_or_else(|| {
                PnmlError::MissingElement(format!(
                    "component sort '{component_sort_id}' for product value"
                ))
            })?;
            let radix = self.sort_cardinality(component_sort)?;
            radices.push(radix);
            total = total
                .checked_mul(radix)
                .ok_or_else(|| PnmlError::UnsupportedNetType {
                    net_type: format!("product sort '{}' cardinality overflow", component_sort_id),
                })?;
        }

        if value >= total {
            return Err(PnmlError::InvalidMarking(format!(
                "product value {value} out of range for cardinality {total}"
            )));
        }

        let mut remaining = value;
        let mut component_values = vec![0usize; component_sort_ids.len()];
        for index in (0..radices.len()).rev() {
            let radix = radices[index];
            component_values[index] = remaining % radix;
            remaining /= radix;
        }
        Ok(component_values)
    }

    /// Find the index of a named constant in a sort.
    ///
    /// Dot sort returns `None` because the dot constant is represented by
    /// `ColorTerm::DotConstant`, not `ColorTerm::UserConstant`. Returning
    /// `Some(0)` here would poison all UserConstant lookups when HashMap
    /// iteration visits the Dot sort first (since any constant_id would
    /// match), causing incorrect guard evaluation.
    pub(super) fn constant_index(&self, sort: &ColorSort, constant_id: &str) -> Option<usize> {
        match sort {
            ColorSort::Dot { .. } => None,
            ColorSort::CyclicEnum { constants, .. } => {
                constants.iter().position(|c| c.id == constant_id)
            }
            ColorSort::Product { .. } => None,
        }
    }

    /// Evaluate a color term to a concrete color value under a binding.
    pub(super) fn eval_color_value(
        &self,
        term: &ColorTerm,
        binding: &HashMap<&str, ColorValue>,
    ) -> Option<ColorValue> {
        match term {
            ColorTerm::Variable(var_id) => binding.get(var_id.as_str()).copied(),
            ColorTerm::Tuple(_) => None,
            ColorTerm::UserConstant(decl_id) => {
                for sort in self.sorts.values() {
                    if let Some(idx) = self.constant_index(sort, decl_id) {
                        return Some(idx);
                    }
                }
                None
            }
            ColorTerm::DotConstant => Some(0),
            ColorTerm::Predecessor(inner) => {
                let val = self.eval_color_value(inner, binding)?;
                let sort = self.sort_for_term(inner)?;
                let card = self.sort_cardinality(sort).ok()?;
                Some(if val == 0 { card - 1 } else { val - 1 })
            }
            ColorTerm::Successor(inner) => {
                let val = self.eval_color_value(inner, binding)?;
                let sort = self.sort_for_term(inner)?;
                let card = self.sort_cardinality(sort).ok()?;
                Some((val + 1) % card)
            }
        }
    }

    pub(super) fn eval_color_value_for_sort(
        &self,
        term: &ColorTerm,
        binding: &HashMap<&str, ColorValue>,
        sort: &ColorSort,
    ) -> Result<Option<ColorValue>, PnmlError> {
        match (sort, term) {
            (ColorSort::Product { components, .. }, ColorTerm::Tuple(component_terms)) => {
                if component_terms.len() != components.len() {
                    return Err(PnmlError::InvalidMarking(format!(
                        "tuple arity {} does not match product sort arity {}",
                        component_terms.len(),
                        components.len()
                    )));
                }

                let mut component_values = Vec::with_capacity(component_terms.len());
                for (component_term, component_sort_id) in
                    component_terms.iter().zip(components.iter())
                {
                    let component_sort = self.sorts.get(component_sort_id).ok_or_else(|| {
                        PnmlError::MissingElement(format!(
                            "component sort '{component_sort_id}' for tuple"
                        ))
                    })?;
                    let component_value = self
                        .eval_color_value_for_sort(component_term, binding, component_sort)?
                        .ok_or_else(|| {
                            PnmlError::InvalidMarking(format!(
                                "tuple component for sort '{component_sort_id}' did not resolve"
                            ))
                        })?;
                    component_values.push(component_value);
                }

                Ok(Some(
                    self.flatten_product_value(components, &component_values)?,
                ))
            }
            (ColorSort::Product { .. }, ColorTerm::Variable(var_id)) => {
                Ok(binding.get(var_id.as_str()).copied())
            }
            _ => Ok(self.eval_color_value(term, binding)),
        }
    }

    /// Determine the sort of a color term (for predecessor/successor wraparound).
    pub(super) fn sort_for_term(&self, term: &ColorTerm) -> Option<&ColorSort> {
        match term {
            ColorTerm::Variable(var_id) => self.sort_for_variable(var_id).ok(),
            ColorTerm::UserConstant(decl_id) => {
                for sort in self.sorts.values() {
                    if self.constant_index(sort, decl_id).is_some() {
                        return Some(sort);
                    }
                }
                None
            }
            ColorTerm::DotConstant => self
                .sorts
                .values()
                .find(|s| matches!(s, ColorSort::Dot { .. })),
            ColorTerm::Tuple(_) => None,
            ColorTerm::Predecessor(inner) | ColorTerm::Successor(inner) => {
                self.sort_for_term(inner)
            }
        }
    }
}
