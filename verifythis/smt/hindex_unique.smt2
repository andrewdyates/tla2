; VerifyThis 2026 Challenge 1: h-index uniqueness (QF_LIA)
; Andrew Yates <andrewyates.name@gmail.com>
; Copyright 2026 Andrew Yates. License: Apache-2.0
;
; PROPERTY 2: The h-index is unique.
;
; Key insight: count_ge(a, v) is monotone decreasing in v (for sorted arrays).
; If h1 < h2 both satisfy the h-index definition:
;   count_ge(a, h1+1) < h1+1   (from h1 being h-index)
;   count_ge(a, h2) >= h2       (from h2 being h-index)
; But h2 >= h1+1 (since h2 > h1, both integers), so:
;   count_ge(a, h2) <= count_ge(a, h1+1)  (monotonicity)
;   => h2 <= count_ge(a, h2) <= count_ge(a, h1+1) < h1+1 <= h2
;   => h2 < h2, contradiction.
;
; We encode just this core argument in QF_LIA.
; WLOG assume h1 < h2 (the other case is symmetric).

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

; Two candidate values, h1 < h2
(declare-const h1 Int)
(declare-const h2 Int)
(assert (>= h1 0))
(assert (<= h2 5))
(assert (< h1 h2))

; count_ge(a, h1+1): number of elements >= h1+1
(declare-const p0 Int)
(declare-const p1 Int)
(declare-const p2 Int)
(declare-const p3 Int)
(declare-const p4 Int)
(assert (=> (>= a0 (+ h1 1)) (= p0 1)))
(assert (=> (< a0 (+ h1 1)) (= p0 0)))
(assert (=> (>= a1 (+ h1 1)) (= p1 1)))
(assert (=> (< a1 (+ h1 1)) (= p1 0)))
(assert (=> (>= a2 (+ h1 1)) (= p2 1)))
(assert (=> (< a2 (+ h1 1)) (= p2 0)))
(assert (=> (>= a3 (+ h1 1)) (= p3 1)))
(assert (=> (< a3 (+ h1 1)) (= p3 0)))
(assert (=> (>= a4 (+ h1 1)) (= p4 1)))
(assert (=> (< a4 (+ h1 1)) (= p4 0)))

(declare-const cnt_h1p1 Int)
(assert (= cnt_h1p1 (+ p0 p1 p2 p3 p4)))

; h1 satisfies: count_ge(a, h1+1) < h1+1
(assert (< cnt_h1p1 (+ h1 1)))

; count_ge(a, h2): number of elements >= h2
(declare-const q0 Int)
(declare-const q1 Int)
(declare-const q2 Int)
(declare-const q3 Int)
(declare-const q4 Int)
(assert (=> (>= a0 h2) (= q0 1)))
(assert (=> (< a0 h2) (= q0 0)))
(assert (=> (>= a1 h2) (= q1 1)))
(assert (=> (< a1 h2) (= q1 0)))
(assert (=> (>= a2 h2) (= q2 1)))
(assert (=> (< a2 h2) (= q2 0)))
(assert (=> (>= a3 h2) (= q3 1)))
(assert (=> (< a3 h2) (= q3 0)))
(assert (=> (>= a4 h2) (= q4 1)))
(assert (=> (< a4 h2) (= q4 0)))

(declare-const cnt_h2 Int)
(assert (= cnt_h2 (+ q0 q1 q2 q3 q4)))

; h2 satisfies: count_ge(a, h2) >= h2
(assert (>= cnt_h2 h2))

; Monotonicity: since h2 >= h1+1, count_ge(a, h2) <= count_ge(a, h1+1)
; For each element: a[i] >= h2 implies a[i] >= h1+1 (since h2 >= h1+1)
; So q[i] <= p[i] for each i
(assert (<= q0 p0))
(assert (<= q1 p1))
(assert (<= q2 p2))
(assert (<= q3 p3))
(assert (<= q4 p4))

; Now we have:
;   h2 <= cnt_h2 <= cnt_h1p1 < h1+1 <= h2
; This is contradictory. UNSAT = uniqueness holds.

(check-sat)
