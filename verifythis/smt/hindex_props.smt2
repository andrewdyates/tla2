; VerifyThis 2026 Challenge 1: h-index validity (QF_LIA)
; Andrew Yates <andrewyates.name@gmail.com>
; Copyright 2026 Andrew Yates. License: Apache-2.0
;
; PROPERTY 1: compute returns a valid h-index for a reverse-sorted array.
;   count_ge(a, h) >= h AND count_ge(a, h+1) < h+1
;
; Bounded N=5, array a0..a4.
; Approach: enumerate h in {0..5} via case analysis using Bool indicators.
; Avoid nested ite expressions by using Bool->Int via separate assertions.

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

; Compute result h via the linear scan algorithm
; h = max { k in {0..5} : forall j < k, a[j] > j }
; Equivalently: h is determined by the stopping condition.
(declare-const h Int)

; For sorted arrays, a[j] > j iff a[j] >= j+1.
; The scan stops at the first j where a[j] <= j.
; Since the array is sorted, if a[j] <= j then for all k >= j, a[k] <= a[j] <= j <= k.
; So h = min { j : a[j] <= j }, or 5 if no such j exists.

; Encode using indicator variables for "a[j] > j"
(declare-const g0 Int) ; 1 if a0 > 0, else 0
(declare-const g1 Int)
(declare-const g2 Int)
(declare-const g3 Int)
(declare-const g4 Int)

; g0: a0 > 0
(assert (=> (> a0 0) (= g0 1)))
(assert (=> (<= a0 0) (= g0 0)))

; g1: a1 > 1
(assert (=> (> a1 1) (= g1 1)))
(assert (=> (<= a1 1) (= g1 0)))

; g2: a2 > 2
(assert (=> (> a2 2) (= g2 1)))
(assert (=> (<= a2 2) (= g2 0)))

; g3: a3 > 3
(assert (=> (> a3 3) (= g3 1)))
(assert (=> (<= a3 3) (= g3 0)))

; g4: a4 > 4
(assert (=> (> a4 4) (= g4 1)))
(assert (=> (<= a4 4) (= g4 0)))

; The scan is sequential: h counts consecutive passes from the start
; h = 0 if g0 = 0
; h = 1 if g0 = 1 and g1 = 0
; ... etc.
; For sorted arrays, once g[j] = 0, all g[k] = 0 for k > j (by sorted order).
; So h = g0 + g1 + g2 + g3 + g4 (because of the sorted prefix property).
; But this only holds because the array is sorted!
; Let's verify: if a sorted, a[j] > j and a[j+1] <= j+1, then for k > j+1:
; a[k] <= a[j+1] <= j+1 <= k, so a[k] <= k. Correct.
(assert (= h (+ g0 g1 g2 g3 g4)))

; Bound h
(assert (>= h 0))
(assert (<= h 5))

; ============================================================
; count_ge(a, h): number of elements >= h
; count_ge(a, h+1): number of elements >= h+1
; Use separate indicator variables to avoid nested ite.
; ============================================================

(declare-const c0h Int) ; 1 if a0 >= h
(declare-const c1h Int)
(declare-const c2h Int)
(declare-const c3h Int)
(declare-const c4h Int)

(assert (=> (>= a0 h) (= c0h 1)))
(assert (=> (< a0 h) (= c0h 0)))
(assert (=> (>= a1 h) (= c1h 1)))
(assert (=> (< a1 h) (= c1h 0)))
(assert (=> (>= a2 h) (= c2h 1)))
(assert (=> (< a2 h) (= c2h 0)))
(assert (=> (>= a3 h) (= c3h 1)))
(assert (=> (< a3 h) (= c3h 0)))
(assert (=> (>= a4 h) (= c4h 1)))
(assert (=> (< a4 h) (= c4h 0)))

(declare-const cnt_h Int)
(assert (= cnt_h (+ c0h c1h c2h c3h c4h)))

(declare-const c0h1 Int) ; 1 if a0 >= h+1
(declare-const c1h1 Int)
(declare-const c2h1 Int)
(declare-const c3h1 Int)
(declare-const c4h1 Int)

(assert (=> (>= a0 (+ h 1)) (= c0h1 1)))
(assert (=> (< a0 (+ h 1)) (= c0h1 0)))
(assert (=> (>= a1 (+ h 1)) (= c1h1 1)))
(assert (=> (< a1 (+ h 1)) (= c1h1 0)))
(assert (=> (>= a2 (+ h 1)) (= c2h1 1)))
(assert (=> (< a2 (+ h 1)) (= c2h1 0)))
(assert (=> (>= a3 (+ h 1)) (= c3h1 1)))
(assert (=> (< a3 (+ h 1)) (= c3h1 0)))
(assert (=> (>= a4 (+ h 1)) (= c4h1 1)))
(assert (=> (< a4 (+ h 1)) (= c4h1 0)))

(declare-const cnt_h1 Int)
(assert (= cnt_h1 (+ c0h1 c1h1 c2h1 c3h1 c4h1)))

; ============================================================
; NEGATION of P1: NOT (cnt_h >= h AND cnt_h1 < h+1)
; UNSAT means P1 holds universally.
; ============================================================
(assert (or (< cnt_h h) (>= cnt_h1 (+ h 1))))

(check-sat)
