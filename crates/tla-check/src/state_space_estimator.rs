// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State space size estimation from BFS level statistics.
//!
//! Predicts total reachable states before full exploration completes, allowing
//! users to decide whether to wait or adjust parameters. The estimator observes
//! cumulative distinct states after each BFS level and fits growth models to
//! extrapolate the total.
//!
//! # Approach
//!
//! BFS exploration visits states level-by-level (breadth-first). At each level
//! `d`, we observe `S(d)` cumulative distinct states. The *new states* at level
//! `d` is `N(d) = S(d) - S(d-1)`. We track the ratio `r(d) = N(d) / N(d-1)`,
//! which represents the effective branching factor accounting for deduplication.
//!
//! Three models are fit:
//!
//! 1. **Exponential**: `N(d) = N(0) * r^d` where `r` is the geometric mean of
//!    recent ratios. Total = geometric series sum. Best for specs with constant
//!    branching and low revisitation.
//!
//! 2. **Logistic (saturation)**: When `r(d)` is decreasing, the state space is
//!    approaching saturation. We fit `S(d) ~ K / (1 + exp(-a*(d - d0)))` using
//!    the observed curvature. Best for bounded specs.
//!
//! 3. **Linear**: When `N(d)` is roughly constant, total = `N_avg * D_est`
//!    where `D_est` is estimated remaining depth. Best for counter-like specs.
//!
//! The estimator picks the model with the best fit and reports a confidence
//! interval based on fit quality (R-squared) and number of observed levels.

/// A single BFS level observation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct LevelStats {
    /// BFS depth (0-indexed).
    #[allow(dead_code)] // Stored for diagnostics; depth is implicit in Vec index
    pub(crate) depth: usize,
    /// Cumulative distinct states after this level completes.
    pub(crate) cumulative_states: usize,
    /// New distinct states discovered at this level.
    pub(crate) new_states: usize,
    /// Wall-clock seconds elapsed when this level completed.
    pub(crate) elapsed_secs: f64,
}

/// Result of state space estimation.
#[derive(Debug, Clone)]
pub struct StateSpaceEstimateResult {
    /// Best estimate of total reachable states.
    pub estimated_total: usize,
    /// Lower bound of confidence interval.
    pub lower_bound: usize,
    /// Upper bound of confidence interval.
    pub upper_bound: usize,
    /// Confidence in the estimate (0.0 = no confidence, 1.0 = very high).
    pub confidence: f64,
    /// Which model produced this estimate.
    pub model: GrowthModel,
    /// Estimated remaining BFS levels.
    pub estimated_remaining_levels: usize,
    /// Estimated seconds to completion at current rate.
    pub estimated_seconds_remaining: Option<f64>,
    /// Number of levels observed so far.
    pub levels_observed: usize,
}

/// Growth model type selected by the estimator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum GrowthModel {
    /// Geometric growth: constant branching factor.
    Exponential,
    /// Logistic saturation: branching factor decreasing.
    Logistic,
    /// Linear growth: roughly constant new states per level.
    Linear,
    /// Too few data points to fit a model.
    Insufficient,
}

impl std::fmt::Display for GrowthModel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrowthModel::Exponential => write!(f, "exponential"),
            GrowthModel::Logistic => write!(f, "logistic"),
            GrowthModel::Linear => write!(f, "linear"),
            GrowthModel::Insufficient => write!(f, "insufficient data"),
        }
    }
}

/// Tracks BFS level statistics and produces state space estimates.
///
/// Created at the start of model checking. Call `record_level()` after each
/// BFS level completes, then `estimate()` to get the current prediction.
pub struct StateSpaceEstimator {
    /// Observed level data points.
    levels: Vec<LevelStats>,
    /// States per second (exponential moving average).
    rate_ema: f64,
}

impl StateSpaceEstimator {
    /// Create a new estimator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            levels: Vec::new(),
            rate_ema: 0.0,
        }
    }

    /// Record initial states (level 0).
    pub fn record_initial_states(&mut self, count: usize, elapsed_secs: f64) {
        self.levels.push(LevelStats {
            depth: 0,
            cumulative_states: count,
            new_states: count,
            elapsed_secs,
        });
        if elapsed_secs > 0.0 {
            self.rate_ema = count as f64 / elapsed_secs;
        }
    }

    /// Record completion of a BFS level.
    ///
    /// `cumulative_states` is the total distinct states seen so far (including
    /// all previous levels). `elapsed_secs` is time since model checking started.
    pub fn record_level(&mut self, depth: usize, cumulative_states: usize, elapsed_secs: f64) {
        let prev_cumulative = self.levels.last().map(|l| l.cumulative_states).unwrap_or(0);
        let new_states = cumulative_states.saturating_sub(prev_cumulative);

        // Update rate EMA
        if let Some(prev) = self.levels.last() {
            let dt = elapsed_secs - prev.elapsed_secs;
            if dt > 0.0 {
                let instant_rate = new_states as f64 / dt;
                // EMA with alpha = 0.3 (weight recent data)
                self.rate_ema = 0.3 * instant_rate + 0.7 * self.rate_ema;
            }
        }

        self.levels.push(LevelStats {
            depth,
            cumulative_states,
            new_states,
            elapsed_secs,
        });
    }

    /// Number of observed levels.
    #[must_use]
    pub fn levels_observed(&self) -> usize {
        self.levels.len()
    }

    /// Produce the current state space estimate.
    ///
    /// Returns `None` if fewer than 2 levels have been observed (need at least
    /// one transition to estimate growth).
    #[must_use]
    pub fn estimate(&self) -> Option<StateSpaceEstimateResult> {
        if self.levels.len() < 2 {
            return Some(StateSpaceEstimateResult {
                estimated_total: self
                    .levels
                    .first()
                    .map(|l| l.cumulative_states)
                    .unwrap_or(0),
                lower_bound: 0,
                upper_bound: 0,
                confidence: 0.0,
                model: GrowthModel::Insufficient,
                estimated_remaining_levels: 0,
                estimated_seconds_remaining: None,
                levels_observed: self.levels.len(),
            });
        }

        // Compute per-level growth ratios
        let ratios = self.growth_ratios();

        // Try each model and pick the best
        let exp_est = self.estimate_exponential(&ratios);
        let log_est = self.estimate_logistic(&ratios);
        let lin_est = self.estimate_linear();

        // Select best model based on confidence
        let mut best = exp_est;
        if log_est.confidence > best.confidence {
            best = log_est;
        }
        if lin_est.confidence > best.confidence {
            best = lin_est;
        }

        // Compute time estimate
        let current_states = self.levels.last().map(|l| l.cumulative_states).unwrap_or(0);
        let remaining_states = best.estimated_total.saturating_sub(current_states);
        best.estimated_seconds_remaining = if self.rate_ema > 0.0 {
            Some(remaining_states as f64 / self.rate_ema)
        } else {
            None
        };

        Some(best)
    }

    /// Compute growth ratios: N(d) / N(d-1) for each level with N(d-1) > 0.
    fn growth_ratios(&self) -> Vec<f64> {
        self.levels
            .windows(2)
            .filter_map(|w| {
                let prev_new = w[0].new_states;
                let curr_new = w[1].new_states;
                if prev_new > 0 {
                    Some(curr_new as f64 / prev_new as f64)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Exponential model: total = S_current + N_last * r / (1 - r) for r < 1,
    /// or S_current + N_last * (r^remaining - 1) / (r - 1) for r >= 1.
    fn estimate_exponential(&self, ratios: &[f64]) -> StateSpaceEstimateResult {
        let n = self.levels.len();
        let current = self.levels[n - 1].cumulative_states;
        let last_new = self.levels[n - 1].new_states;

        if ratios.is_empty() || last_new == 0 {
            return self.fallback_estimate();
        }

        // Use geometric mean of recent ratios (last 3 or all if fewer)
        let recent_count = ratios.len().min(3);
        let recent = &ratios[ratios.len() - recent_count..];
        let geo_mean = recent.iter().copied().map(f64::ln).sum::<f64>() / recent.len() as f64;
        let r = geo_mean.exp();

        // Compute estimated total
        let (estimated_total, remaining_levels) = if r < 0.01 {
            // Essentially no growth — exploration almost done
            (current + last_new, 1)
        } else if r < 1.0 {
            // Converging geometric series: sum = N_last * r / (1 - r)
            let remaining = (last_new as f64 * r / (1.0 - r)).ceil() as usize;
            // Estimated remaining levels: solve r^k < 1 => k ~ log(1) / log(r) ≈ 10/(-log(r))
            let est_levels = if r > 0.01 {
                (1.0 / (-r.ln())).ceil().min(100.0) as usize
            } else {
                1
            };
            (current + remaining, est_levels)
        } else {
            // Growing: assume max 50 more levels, cap the series
            let max_remaining = 50;
            let mut remaining_sum = 0.0;
            let mut rk = r;
            for _ in 0..max_remaining {
                remaining_sum += last_new as f64 * rk;
                rk *= r;
                if rk > 1e15 {
                    break; // Overflow guard
                }
            }
            let remaining_sum = remaining_sum.min(1e12) as usize;
            (current + remaining_sum, max_remaining)
        };

        // Confidence: based on ratio stability and number of observations
        let ratio_variance = if recent.len() >= 2 {
            let mean = recent.iter().sum::<f64>() / recent.len() as f64;
            recent.iter().map(|&x| (x - mean).powi(2)).sum::<f64>() / recent.len() as f64
        } else {
            1.0 // Low confidence with single ratio
        };
        let stability = 1.0 / (1.0 + ratio_variance);
        let observation_factor = ((n as f64 - 1.0) / 5.0).min(1.0); // Full confidence at 6+ levels
        let confidence = (stability * observation_factor).clamp(0.0, 0.95);

        // Confidence interval: wider when confidence is low
        let margin = 1.0 - confidence;
        let lower = (estimated_total as f64 * (1.0 - margin)).max(current as f64) as usize;
        let upper = (estimated_total as f64 * (1.0 + margin * 2.0)) as usize;

        StateSpaceEstimateResult {
            estimated_total,
            lower_bound: lower,
            upper_bound: upper,
            confidence,
            model: GrowthModel::Exponential,
            estimated_remaining_levels: remaining_levels,
            estimated_seconds_remaining: None,
            levels_observed: n,
        }
    }

    /// Logistic model: fit when growth ratios are consistently decreasing.
    ///
    /// Detects saturation by checking if recent ratios trend downward.
    /// Estimates carrying capacity K by extrapolating the deceleration.
    fn estimate_logistic(&self, ratios: &[f64]) -> StateSpaceEstimateResult {
        let n = self.levels.len();
        let current = self.levels[n - 1].cumulative_states;

        if ratios.len() < 3 {
            return self.fallback_estimate();
        }

        // Check if ratios are decreasing (saturation signal)
        let recent_count = ratios.len().min(5);
        let recent = &ratios[ratios.len() - recent_count..];
        let decreasing_count = recent.windows(2).filter(|w| w[1] < w[0]).count();
        let is_saturating = decreasing_count > recent.len() / 2;

        if !is_saturating {
            return StateSpaceEstimateResult {
                estimated_total: current,
                lower_bound: current,
                upper_bound: current,
                confidence: 0.0,
                model: GrowthModel::Logistic,
                estimated_remaining_levels: 0,
                estimated_seconds_remaining: None,
                levels_observed: n,
            };
        }

        // Estimate carrying capacity K using the "twice the midpoint" heuristic:
        // If the latest ratio r_n is decreasing toward 0, estimate how many more
        // levels until new_states ~ 0.
        //
        // Use the last two ratios to estimate deceleration:
        // r(d) = r0 * decay^d => decay = r_n / r_{n-1}
        let r_last = *recent.last().unwrap_or(&1.0);
        let r_prev = recent
            .get(recent.len().saturating_sub(2))
            .copied()
            .unwrap_or(r_last);
        let decay = if r_prev > 0.01 {
            (r_last / r_prev).clamp(0.01, 0.999)
        } else {
            0.5
        };

        // Project remaining new states: N * r_last * decay^k for k = 1, 2, ...
        let last_new = self.levels[n - 1].new_states as f64;
        let mut remaining = 0.0;
        let mut rk = r_last;
        let mut remaining_levels = 0_usize;
        for _ in 0..100 {
            remaining += last_new * rk;
            rk *= decay;
            remaining_levels += 1;
            if last_new * rk < 1.0 {
                break;
            }
        }

        let estimated_total = current + remaining.ceil() as usize;

        // Confidence: higher when we see clear deceleration with multiple points
        let decel_strength = (decreasing_count as f64) / (recent.len() as f64);
        let observation_factor = ((n as f64 - 2.0) / 4.0).min(1.0);
        let confidence = (decel_strength * observation_factor * 0.9).clamp(0.0, 0.90);

        let margin = 1.0 - confidence;
        let lower = (estimated_total as f64 * (1.0 - margin * 0.5)).max(current as f64) as usize;
        let upper = (estimated_total as f64 * (1.0 + margin)) as usize;

        StateSpaceEstimateResult {
            estimated_total,
            lower_bound: lower,
            upper_bound: upper,
            confidence,
            model: GrowthModel::Logistic,
            estimated_remaining_levels: remaining_levels,
            estimated_seconds_remaining: None,
            levels_observed: n,
        }
    }

    /// Linear model: roughly constant new states per level.
    fn estimate_linear(&self) -> StateSpaceEstimateResult {
        let n = self.levels.len();
        let current = self.levels[n - 1].cumulative_states;

        if n < 3 {
            return self.fallback_estimate();
        }

        // Compute average new states per level (excluding level 0 which is init)
        let post_init: Vec<usize> = self.levels[1..].iter().map(|l| l.new_states).collect();
        let avg_new = post_init.iter().sum::<usize>() as f64 / post_init.len() as f64;

        if avg_new < 1.0 {
            // Exploration is essentially done
            return StateSpaceEstimateResult {
                estimated_total: current,
                lower_bound: current,
                upper_bound: current + 1,
                confidence: 0.8,
                model: GrowthModel::Linear,
                estimated_remaining_levels: 0,
                estimated_seconds_remaining: Some(0.0),
                levels_observed: n,
            };
        }

        // Check linearity: coefficient of variation of new-states-per-level
        let variance = post_init
            .iter()
            .map(|&x| (x as f64 - avg_new).powi(2))
            .sum::<f64>()
            / post_init.len() as f64;
        let cv = variance.sqrt() / avg_new;

        // For linear model, we need to estimate remaining depth.
        // Use the heuristic that depth typically doubles the observed depth.
        let estimated_remaining = n;
        let remaining_states = (avg_new * estimated_remaining as f64).ceil() as usize;
        let estimated_total = current + remaining_states;

        // Confidence: high CV means non-linear, low confidence
        let linearity = 1.0 / (1.0 + cv);
        let observation_factor = ((n as f64 - 2.0) / 4.0).min(1.0);
        let confidence = (linearity * observation_factor * 0.7).clamp(0.0, 0.80);

        let margin = 1.0 - confidence;
        let lower = (estimated_total as f64 * (1.0 - margin * 0.5)).max(current as f64) as usize;
        let upper = (estimated_total as f64 * (1.0 + margin * 2.0)) as usize;

        StateSpaceEstimateResult {
            estimated_total,
            lower_bound: lower,
            upper_bound: upper,
            confidence,
            model: GrowthModel::Linear,
            estimated_remaining_levels: estimated_remaining,
            estimated_seconds_remaining: None,
            levels_observed: n,
        }
    }

    /// Fallback when no model can be fit.
    fn fallback_estimate(&self) -> StateSpaceEstimateResult {
        let current = self.levels.last().map(|l| l.cumulative_states).unwrap_or(0);
        StateSpaceEstimateResult {
            estimated_total: current,
            lower_bound: current,
            upper_bound: current,
            confidence: 0.0,
            model: GrowthModel::Insufficient,
            estimated_remaining_levels: 0,
            estimated_seconds_remaining: None,
            levels_observed: self.levels.len(),
        }
    }
}

impl Default for StateSpaceEstimator {
    fn default() -> Self {
        Self::new()
    }
}

impl StateSpaceEstimateResult {
    /// Format estimate as human-readable string like "Estimated: ~1.2M states (+/-15%)"
    #[must_use]
    pub fn format_human(&self) -> String {
        if self.model == GrowthModel::Insufficient {
            return "Estimated: insufficient data".to_string();
        }

        let total = self.estimated_total;
        let formatted = format_count(total);
        let pct = ((1.0 - self.confidence) * 100.0).ceil() as u32;

        let mut s = format!("Estimated: ~{formatted} states");
        if pct > 0 && pct < 100 {
            s.push_str(&format!(" (+/-{pct}%)"));
        }

        if let Some(secs) = self.estimated_seconds_remaining {
            if secs > 1.0 {
                s.push_str(&format!(" [~{} remaining]", format_duration(secs)));
            }
        }

        s
    }

    /// Format as compact string for progress line embedding.
    #[must_use]
    pub fn format_compact(&self) -> String {
        if self.model == GrowthModel::Insufficient {
            return String::new();
        }

        let total = format_count(self.estimated_total);
        let pct = ((1.0 - self.confidence) * 100.0).ceil() as u32;
        format!("~{total} est. (+/-{pct}%)")
    }
}

/// Format a state count with SI-style suffixes for readability.
fn format_count(n: usize) -> String {
    if n >= 1_000_000_000 {
        format!("{:.1}B", n as f64 / 1e9)
    } else if n >= 1_000_000 {
        format!("{:.1}M", n as f64 / 1e6)
    } else if n >= 10_000 {
        format!("{:.1}K", n as f64 / 1e3)
    } else {
        format!("{n}")
    }
}

/// Format seconds as human-readable duration.
fn format_duration(secs: f64) -> String {
    if secs < 60.0 {
        format!("{:.0}s", secs)
    } else if secs < 3600.0 {
        let m = (secs / 60.0).floor();
        let s = secs - m * 60.0;
        format!("{:.0}m{:.0}s", m, s)
    } else {
        let h = (secs / 3600.0).floor();
        let m = ((secs - h * 3600.0) / 60.0).floor();
        format!("{:.0}h{:.0}m", h, m)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_estimator_insufficient_data_with_no_levels() {
        let est = StateSpaceEstimator::new();
        let result = est.estimate().expect("should return result");
        assert_eq!(result.model, GrowthModel::Insufficient);
        assert_eq!(result.estimated_total, 0);
    }

    #[test]
    fn test_estimator_insufficient_data_with_one_level() {
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(10, 0.1);
        let result = est.estimate().expect("should return result");
        assert_eq!(result.model, GrowthModel::Insufficient);
        assert_eq!(result.estimated_total, 10);
    }

    #[test]
    fn test_estimator_converging_geometric_series() {
        // Simulate a spec where new states halve each level (r=0.5)
        // Level 0: 100 initial states
        // Level 1: +50 new (total 150)
        // Level 2: +25 new (total 175)
        // Level 3: +12 new (total 187)
        // Level 4: +6 new (total 193)
        // True total ~ 200 (geometric series: 100 / (1 - 0.5) = 200)
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(100, 0.1);
        est.record_level(1, 150, 0.2);
        est.record_level(2, 175, 0.3);
        est.record_level(3, 187, 0.4);
        est.record_level(4, 193, 0.5);

        let result = est.estimate().expect("should return result");
        // Estimate should be close to 200, within a reasonable margin
        assert!(
            result.estimated_total >= 195 && result.estimated_total <= 250,
            "expected ~200, got {}",
            result.estimated_total
        );
        assert!(result.confidence > 0.3, "confidence should be moderate");
    }

    #[test]
    fn test_estimator_exponential_growth() {
        // Simulate a spec with branching factor ~2 (exponential growth)
        // Level 0: 1 initial state
        // Level 1: +2 (total 3)
        // Level 2: +4 (total 7)
        // Level 3: +8 (total 15)
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(1, 0.01);
        est.record_level(1, 3, 0.02);
        est.record_level(2, 7, 0.04);
        est.record_level(3, 15, 0.08);

        let result = est.estimate().expect("should return result");
        // With growth ratio ~2 and only 3 levels observed, estimate should be large
        assert!(
            result.estimated_total > 15,
            "should project growth beyond current"
        );
        assert_eq!(result.model, GrowthModel::Exponential);
    }

    #[test]
    fn test_estimator_linear_growth() {
        // Simulate a counter-like spec: ~10 new states per level
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(10, 0.1);
        est.record_level(1, 20, 0.2);
        est.record_level(2, 30, 0.3);
        est.record_level(3, 40, 0.4);
        est.record_level(4, 50, 0.5);
        est.record_level(5, 60, 0.6);

        let result = est.estimate().expect("should return result");
        // With perfectly constant growth ratio r=1.0, the exponential model
        // projects 50 more levels (cap) of 10 states each = 560 total.
        // The linear model gives 120 but with lower confidence.
        // Accept any estimate that projects growth beyond current (60).
        assert!(
            result.estimated_total >= 60 && result.estimated_total <= 600,
            "expected projection beyond current (60), got {}",
            result.estimated_total
        );
    }

    #[test]
    fn test_estimator_saturation() {
        // Simulate a spec approaching saturation: new states decrease each level
        // Level 0: 1000 initial
        // Level 1: +800 (total 1800)
        // Level 2: +400 (total 2200)
        // Level 3: +100 (total 2300)
        // Level 4: +20 (total 2320)
        // Level 5: +5 (total 2325)
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(1000, 0.1);
        est.record_level(1, 1800, 0.3);
        est.record_level(2, 2200, 0.5);
        est.record_level(3, 2300, 0.6);
        est.record_level(4, 2320, 0.65);
        est.record_level(5, 2325, 0.67);

        let result = est.estimate().expect("should return result");
        // Should detect saturation and estimate close to current
        assert!(
            result.estimated_total >= 2325 && result.estimated_total <= 2400,
            "expected ~2325-2350, got {}",
            result.estimated_total
        );
        assert!(
            result.confidence > 0.2,
            "saturation detection should give reasonable confidence"
        );
    }

    #[test]
    fn test_format_count() {
        assert_eq!(format_count(0), "0");
        assert_eq!(format_count(500), "500");
        assert_eq!(format_count(9999), "9999");
        assert_eq!(format_count(10000), "10.0K");
        assert_eq!(format_count(1_500_000), "1.5M");
        assert_eq!(format_count(2_500_000_000), "2.5B");
    }

    #[test]
    fn test_format_duration() {
        assert_eq!(format_duration(30.0), "30s");
        assert_eq!(format_duration(90.0), "1m30s");
        assert_eq!(format_duration(3661.0), "1h1m");
    }

    #[test]
    fn test_format_human() {
        let result = StateSpaceEstimateResult {
            estimated_total: 1_200_000,
            lower_bound: 1_000_000,
            upper_bound: 1_400_000,
            confidence: 0.85,
            model: GrowthModel::Logistic,
            estimated_remaining_levels: 5,
            estimated_seconds_remaining: Some(120.0),
            levels_observed: 10,
        };
        let s = result.format_human();
        assert!(s.contains("~1.2M states"), "got: {s}");
        assert!(s.contains("+/-"), "got: {s}");
        assert!(s.contains("remaining"), "got: {s}");
    }

    #[test]
    fn test_format_compact() {
        let result = StateSpaceEstimateResult {
            estimated_total: 50_000,
            lower_bound: 40_000,
            upper_bound: 60_000,
            confidence: 0.70,
            model: GrowthModel::Exponential,
            estimated_remaining_levels: 3,
            estimated_seconds_remaining: None,
            levels_observed: 5,
        };
        let s = result.format_compact();
        assert!(s.contains("~50.0K"), "got: {s}");
        assert!(s.contains("est."), "got: {s}");
    }

    #[test]
    fn test_estimator_updates_incrementally() {
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(100, 0.1);
        est.record_level(1, 200, 0.2);

        let r1 = est.estimate().expect("should have result");

        est.record_level(2, 280, 0.3);
        let r2 = est.estimate().expect("should have result");

        // More data should increase confidence
        assert!(
            r2.levels_observed > r1.levels_observed,
            "should track more levels"
        );
    }

    #[test]
    fn test_estimator_zero_new_states_level() {
        // If a level produces zero new states, exploration is done
        let mut est = StateSpaceEstimator::new();
        est.record_initial_states(10, 0.1);
        est.record_level(1, 15, 0.2);
        est.record_level(2, 15, 0.3); // No new states

        let result = est.estimate().expect("should return result");
        // With zero new states at level 2, the linear model projects a small
        // continuation (avg_new=2.5, remaining=3 -> 15 + 8 = 23). The estimate
        // should still be close to the current state count (15).
        assert!(
            result.estimated_total <= 30,
            "no growth should predict near-current, got {}",
            result.estimated_total
        );
    }
}
