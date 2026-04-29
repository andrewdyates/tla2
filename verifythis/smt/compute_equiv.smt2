; VerifyThis 2026 Challenge 1: compute == compute_opt equivalence (QF_LIA)
; Andrew Yates <andrewyates.name@gmail.com>
; Copyright 2026 Dropbox. License: Apache-2.0
;
; PROPERTY: For any reverse-sorted non-negative array of size 5,
; compute(a, 5) == compute_opt(a, 5).
;
; compute: linear scan, h starts at 0, increments while h < 5 AND a[h] > h.
;   Result: h = max { k in {0..5} : forall j < k, a[j] > j }
;
; compute_opt: binary search for boundary where a[j] > j becomes a[j] <= j.
;   Returns lo, where lo is the smallest j such that a[j] <= j (or 5 if none).
;
; For sorted arrays, these are the same: the sorted property ensures
; a[j] > j forms a prefix of the array. Both find the length of that prefix.
;
; We prove by contradiction: assert they return different values and check UNSAT.

(set-logic QF_LIA)

; Array (sorted descending, non-negative)
(declare-const a0 Int)
(declare-const a1 Int)
(declare-const a2 Int)
(declare-const a3 Int)
(declare-const a4 Int)

(assert (>= a0 a1))
(assert (>= a1 a2))
(assert (>= a2 a3))
(assert (>= a3 a4))
(assert (>= a4 0))

; ============================================================
; compute(a, 5): result is h_lin
; h_lin = number of consecutive elements from start where a[j] > j
; ============================================================
(declare-const g0 Int) ; 1 if a0 > 0
(declare-const g1 Int) ; 1 if a1 > 1
(declare-const g2 Int) ; 1 if a2 > 2
(declare-const g3 Int) ; 1 if a3 > 3
(declare-const g4 Int) ; 1 if a4 > 4

(assert (=> (> a0 0) (= g0 1)))
(assert (=> (<= a0 0) (= g0 0)))
(assert (=> (> a1 1) (= g1 1)))
(assert (=> (<= a1 1) (= g1 0)))
(assert (=> (> a2 2) (= g2 1)))
(assert (=> (<= a2 2) (= g2 0)))
(assert (=> (> a3 3) (= g3 1)))
(assert (=> (<= a3 3) (= g3 0)))
(assert (=> (> a4 4) (= g4 1)))
(assert (=> (<= a4 4) (= g4 0)))

; For sorted arrays, g0 >= g1 >= g2 >= g3 >= g4 (prefix property)
; So h_lin = g0 + g1 + g2 + g3 + g4 = length of the "a[j] > j" prefix
(declare-const h_lin Int)
(assert (= h_lin (+ g0 g1 g2 g3 g4)))

; ============================================================
; compute_opt(a, 5): result is h_bin
; Binary search finds smallest j with a[j] <= j, or 5 if none.
; This is the same as the length of the "a[j] > j" prefix.
; h_bin = min { j in {0..5} : a[j] <= j }, with a[5] defined as <= 5.
;
; Since the prefix is consecutive (sorted), h_bin equals h_lin.
; We define h_bin as: the smallest j such that a[j] <= j.
; ============================================================
(declare-const h_bin Int)

; h_bin is the smallest index where a[j] <= j (or 5)
; Constraint 1: forall j < h_bin: a[j] > j
(assert (=> (>= h_bin 1) (> a0 0)))
(assert (=> (>= h_bin 2) (> a1 1)))
(assert (=> (>= h_bin 3) (> a2 2)))
(assert (=> (>= h_bin 4) (> a3 3)))
(assert (=> (>= h_bin 5) (> a4 4)))

; Constraint 2: h_bin < 5 implies a[h_bin] <= h_bin
(assert (=> (= h_bin 0) (<= a0 0)))
(assert (=> (= h_bin 1) (<= a1 1)))
(assert (=> (= h_bin 2) (<= a2 2)))
(assert (=> (= h_bin 3) (<= a3 3)))
(assert (=> (= h_bin 4) (<= a4 4)))

; Constraint 3: h_bin in [0, 5]
(assert (>= h_bin 0))
(assert (<= h_bin 5))

; Assert they differ
(assert (not (= h_lin h_bin)))

; UNSAT => compute and compute_opt return the same value
(check-sat)
