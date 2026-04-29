// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Frame management for IC3/PDR.
//!
//! IC3 maintains a sequence of frames F_0, F_1, ..., F_k where:
//! - F_0 = Init (initial states)
//! - Each frame F_i is an over-approximation of states reachable in at most i steps
//! - F_i => F_{i+1} (frames are monotonically weaker)
//! - The property holds in every frame
//!
//! A frame stores a set of *lemmas* (blocking clauses). A lemma is a clause
//! (disjunction of literals) that is true in all states of that frame.
//! Equivalently, the negation of a lemma is a *cube* (state) that is blocked.
//!
//! Reference: Aaron R. Bradley, "SAT-Based Model Checking without Unrolling" (VMCAI 2011).

use crate::sat_types::Lit;

/// A lemma (blocking clause): a disjunction of literals that must hold
/// in all states of the frame it belongs to.
///
/// Stored in sorted order for efficient subsumption checks.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lemma {
    /// Clause literals, sorted by code for canonical form.
    pub lits: Vec<Lit>,
}

impl Lemma {
    /// Create a new lemma from a set of literals (will be sorted).
    pub fn new(mut lits: Vec<Lit>) -> Self {
        lits.sort_by_key(|l| l.code());
        lits.dedup();
        Lemma { lits }
    }

    /// Create a blocking clause from a cube (conjunction) to block.
    /// The lemma is the negation of the cube: negate each literal.
    pub fn from_blocked_cube(cube: &[Lit]) -> Self {
        let lits: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        Lemma::new(lits)
    }

    /// Check if this lemma subsumes `other`.
    /// A clause C subsumes D if every literal in C also appears in D.
    /// (C is a subset of D, meaning C is stronger/more general.)
    pub fn subsumes(&self, other: &Lemma) -> bool {
        if self.lits.len() > other.lits.len() {
            return false;
        }
        // Since both are sorted by code, we can do a merge-style check.
        let mut j = 0;
        for &lit in &self.lits {
            while j < other.lits.len() && other.lits[j].code() < lit.code() {
                j += 1;
            }
            if j >= other.lits.len() || other.lits[j] != lit {
                return false;
            }
            j += 1;
        }
        true
    }
}

/// A single frame in the IC3 frame sequence.
#[derive(Debug, Clone, Default)]
pub struct Frame {
    /// Lemmas (blocking clauses) in this frame.
    pub lemmas: Vec<Lemma>,
}

impl Frame {
    pub fn new() -> Self {
        Frame { lemmas: Vec::new() }
    }

    /// Check if any existing lemma subsumes the given one.
    pub fn has_subsuming(&self, lemma: &Lemma) -> bool {
        self.lemmas.iter().any(|l| l.subsumes(lemma))
    }
}

/// The sequence of frames F_1, F_2, ..., F_k maintained by IC3.
///
/// Frame 0 (init) is handled implicitly through the init constraints.
/// `frames[0]` corresponds to F_1 in the IC3 literature.
#[derive(Debug, Clone)]
pub struct Frames {
    /// The frame sequence. `frames[i]` = F_{i+1}.
    pub frames: Vec<Frame>,
}

impl Frames {
    pub fn new() -> Self {
        Frames { frames: Vec::new() }
    }

    /// Current depth (number of frames).
    #[inline]
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    /// Push a new empty frame.
    pub fn push_new(&mut self) {
        self.frames.push(Frame::new());
    }

    /// Add a lemma to a specific frame level.
    ///
    /// Returns `true` if the lemma was actually added, `false` if it was
    /// redundant (an existing lemma already subsumes it).
    ///
    /// When added, any existing lemmas subsumed by the new one are removed.
    pub fn add_lemma(&mut self, level: usize, lemma: Lemma) -> bool {
        if level < self.frames.len() {
            // Forward subsumption: if an existing lemma already subsumes the new one,
            // the new lemma is redundant — skip it entirely.
            if self.frames[level].has_subsuming(&lemma) {
                return false;
            }
            // Backward subsumption: remove any lemmas that the new one subsumes.
            self.frames[level]
                .lemmas
                .retain(|existing| !lemma.subsumes(existing));
            self.frames[level].lemmas.push(lemma);
            true
        } else {
            false
        }
    }

    /// Find a "parent lemma" in frame-1 that subsumes the negation of the cube.
    ///
    /// When generalizing a cube at frame `frame`, a parent lemma is a blocking
    /// clause from the previous frame whose negation (cube) is a subset of the
    /// current cube. Literals present in the parent lemma should be preserved
    /// during MIC (tried for removal last), as reusing structure from already-
    /// proven lemmas tends to produce more general and reusable clauses.
    ///
    /// Reference: rIC3 `frame.rs:124` — `parent_lemma()`.
    /// Reference: CAV'23 parent lemma heuristic for IC3 generalization.
    pub fn parent_lemma(&self, cube: &[Lit], frame: usize) -> Option<Vec<Lit>> {
        if frame <= 1 || frame > self.frames.len() {
            return None;
        }
        // Look in the frame BELOW the current one (frame - 2 because frames[0] = F_1).
        let prev_frame_idx = frame - 2;
        if prev_frame_idx >= self.frames.len() {
            return None;
        }
        // Build the blocking clause for the current cube.
        let cube_clause = Lemma::from_blocked_cube(cube);
        // Find a lemma in the previous frame that subsumes our cube's clause.
        for lemma in &self.frames[prev_frame_idx].lemmas {
            if lemma.subsumes(&cube_clause) {
                // Convert the parent lemma back to cube form (negate each literal).
                let parent_cube: Vec<Lit> = lemma.lits.iter().map(|l| !*l).collect();
                return Some(parent_cube);
            }
        }
        None
    }

    /// Check if a cube is already blocked at the given frame level or higher.
    /// A cube is blocked if there exists a lemma whose negation subsumes the cube.
    pub fn is_blocked(&self, level: usize, cube: &[Lit]) -> bool {
        let clause = Lemma::from_blocked_cube(cube);
        for i in level..self.frames.len() {
            if self.frames[i].has_subsuming(&clause) {
                return true;
            }
        }
        false
    }

    /// Check convergence: does any frame F_k have no lemmas?
    /// If so, all reachable states are characterized by the invariant and the property is proved.
    pub fn check_convergence(&self) -> Option<usize> {
        for (i, frame) in self.frames.iter().enumerate() {
            if i > 0 && frame.lemmas.is_empty() {
                return Some(i);
            }
        }
        None
    }
}

impl Default for Frames {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_types::Var;

    #[test]
    fn test_lemma_subsumption() {
        // {a, b} subsumes {a, b, c}
        let l1 = Lemma::new(vec![Lit::pos(Var(1)), Lit::pos(Var(2))]);
        let l2 = Lemma::new(vec![Lit::pos(Var(1)), Lit::pos(Var(2)), Lit::pos(Var(3))]);
        assert!(l1.subsumes(&l2));
        assert!(!l2.subsumes(&l1));
    }

    #[test]
    fn test_lemma_self_subsumption() {
        let l = Lemma::new(vec![Lit::pos(Var(1)), Lit::neg(Var(2))]);
        assert!(l.subsumes(&l));
    }

    #[test]
    fn test_lemma_no_subsumption() {
        let l1 = Lemma::new(vec![Lit::pos(Var(1))]);
        let l2 = Lemma::new(vec![Lit::neg(Var(1))]);
        assert!(!l1.subsumes(&l2));
    }

    #[test]
    fn test_from_blocked_cube() {
        // Cube: {v1, ~v2}  ->  Clause: {~v1, v2}
        let cube = vec![Lit::pos(Var(1)), Lit::neg(Var(2))];
        let lemma = Lemma::from_blocked_cube(&cube);
        assert_eq!(lemma.lits.len(), 2);
        assert!(lemma.lits.contains(&Lit::neg(Var(1))));
        assert!(lemma.lits.contains(&Lit::pos(Var(2))));
    }

    #[test]
    fn test_frames_add_and_subsume() {
        let mut frames = Frames::new();
        frames.push_new();
        frames.push_new();

        // Add a lemma at level 0.
        let l1 = Lemma::new(vec![Lit::pos(Var(1)), Lit::pos(Var(2))]);
        assert!(frames.add_lemma(0, l1));
        assert_eq!(frames.frames[0].lemmas.len(), 1);

        // Add a more specific lemma — forward subsumption: l1 already subsumes l2,
        // so l2 is redundant and should not be added.
        let l2 = Lemma::new(vec![Lit::pos(Var(1)), Lit::pos(Var(2)), Lit::pos(Var(3))]);
        assert!(!frames.add_lemma(0, l2));
        assert_eq!(frames.frames[0].lemmas.len(), 1);

        // Add a non-overlapping lemma — neither subsumes the other.
        let l_other = Lemma::new(vec![Lit::neg(Var(3)), Lit::pos(Var(4))]);
        assert!(frames.add_lemma(0, l_other));
        assert_eq!(frames.frames[0].lemmas.len(), 2);

        // Add general lemma that subsumes l1 (backward subsumption removes l1).
        let l3 = Lemma::new(vec![Lit::pos(Var(1))]);
        assert!(frames.add_lemma(0, l3));
        // l3 subsumes l1 (removed), but not l_other. Result: l_other + l3 = 2.
        assert_eq!(frames.frames[0].lemmas.len(), 2);
    }

    #[test]
    fn test_convergence_empty_frame() {
        let mut frames = Frames::new();
        frames.push_new(); // F_1
        frames.push_new(); // F_2

        // No lemmas in F_2 => convergence.
        frames.add_lemma(0, Lemma::new(vec![Lit::pos(Var(1))]));
        assert_eq!(frames.check_convergence(), Some(1));
    }

    #[test]
    fn test_is_blocked() {
        let mut frames = Frames::new();
        frames.push_new();

        // Block cube {v1 = true}  =>  lemma {~v1}.
        let cube = vec![Lit::pos(Var(1))];
        let lemma = Lemma::from_blocked_cube(&cube);
        frames.add_lemma(0, lemma);

        // The cube should now be detected as blocked.
        assert!(frames.is_blocked(0, &cube));

        // A different cube should not be blocked.
        let other_cube = vec![Lit::neg(Var(1))];
        assert!(!frames.is_blocked(0, &other_cube));
    }

    #[test]
    fn test_parent_lemma_found() {
        let mut frames = Frames::new();
        frames.push_new(); // F_1 (index 0)
        frames.push_new(); // F_2 (index 1)

        // Block cube {v1=true, v2=true} at F_1 (frame index 0).
        // Lemma = {~v1, ~v2}.
        let cube1 = vec![Lit::pos(Var(1)), Lit::pos(Var(2))];
        let lemma1 = Lemma::from_blocked_cube(&cube1);
        frames.add_lemma(0, lemma1);

        // At frame=2 (which maps to frames[1]), try to find a parent lemma
        // for a cube that extends cube1: {v1=true, v2=true, v3=true}.
        // The parent lemma {~v1, ~v2} subsumes {~v1, ~v2, ~v3}, so
        // the parent cube should be {v1, v2}.
        let cube2 = vec![Lit::pos(Var(1)), Lit::pos(Var(2)), Lit::pos(Var(3))];
        let parent = frames.parent_lemma(&cube2, 2);
        assert!(parent.is_some(), "should find parent lemma");
        let parent_cube = parent.unwrap();
        assert_eq!(parent_cube.len(), 2);
        // Parent cube should contain the negations of the parent lemma
        // (i.e., the original cube literals).
        assert!(parent_cube.contains(&Lit::pos(Var(1))));
        assert!(parent_cube.contains(&Lit::pos(Var(2))));
    }

    #[test]
    fn test_parent_lemma_none_at_frame1() {
        let mut frames = Frames::new();
        frames.push_new(); // F_1

        // At frame=1, there's no frame-0 to look in, so parent_lemma returns None.
        let cube = vec![Lit::pos(Var(1))];
        assert!(frames.parent_lemma(&cube, 1).is_none());
    }

    #[test]
    fn test_parent_lemma_no_match() {
        let mut frames = Frames::new();
        frames.push_new(); // F_1
        frames.push_new(); // F_2

        // Block cube {v1=true} at F_1.
        let cube1 = vec![Lit::pos(Var(1))];
        frames.add_lemma(0, Lemma::from_blocked_cube(&cube1));

        // At frame=2, look for parent of {v2=true, v3=true}.
        // The parent lemma {~v1} does NOT subsume {~v2, ~v3}, so no match.
        let cube2 = vec![Lit::pos(Var(2)), Lit::pos(Var(3))];
        assert!(frames.parent_lemma(&cube2, 2).is_none());
    }
}
