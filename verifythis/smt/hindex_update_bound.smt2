; VerifyThis 2026 Challenge 1: update increment bound (QF_LIA)
; Andrew Yates <andrewyates.name@gmail.com>
; Copyright 2026 Andrew Yates. License: Apache-2.0
;
; PROPERTY 3: Incrementing one citation changes h-index by at most +1.
;
; Given: sorted array a0..a4 with h-index h.
; After: increment one element by 1 and re-sort to get b0..b4.
; Claim: h-index of b is at most h+1.
;
; Proof sketch: incrementing one element by 1 increases count_ge(a, v)
; by at most 1 for any v. For h' >= h+2 to be a valid h-index, we need
; count_ge(b, h+2) >= h+2. But count_ge(b, h+2) <= count_ge(a, h+2) + 1.
; And count_ge(a, h+2) <= count_ge(a, h+1) < h+1. So count_ge(b, h+2) < h+2.
;
; Bounded N=5. We assert existence of arrays where h-index jumps by 2+ and check UNSAT.

(set-logic QF_LIA)

; Original array (sorted descending, non-negative)
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

; h-index of original array
(declare-const h Int)
(assert (>= h 0))
(assert (<= h 5))

; h satisfies h-index definition: count_ge(a,h) >= h
(declare-const ch0 Int)
(declare-const ch1 Int)
(declare-const ch2 Int)
(declare-const ch3 Int)
(declare-const ch4 Int)

(assert (=> (>= a0 h) (= ch0 1)))
(assert (=> (< a0 h) (= ch0 0)))
(assert (=> (>= a1 h) (= ch1 1)))
(assert (=> (< a1 h) (= ch1 0)))
(assert (=> (>= a2 h) (= ch2 1)))
(assert (=> (< a2 h) (= ch2 0)))
(assert (=> (>= a3 h) (= ch3 1)))
(assert (=> (< a3 h) (= ch3 0)))
(assert (=> (>= a4 h) (= ch4 1)))
(assert (=> (< a4 h) (= ch4 0)))
(assert (>= (+ ch0 ch1 ch2 ch3 ch4) h))

; count_ge(a, h+1) < h+1
(declare-const ch10 Int)
(declare-const ch11 Int)
(declare-const ch12 Int)
(declare-const ch13 Int)
(declare-const ch14 Int)

(assert (=> (>= a0 (+ h 1)) (= ch10 1)))
(assert (=> (< a0 (+ h 1)) (= ch10 0)))
(assert (=> (>= a1 (+ h 1)) (= ch11 1)))
(assert (=> (< a1 (+ h 1)) (= ch11 0)))
(assert (=> (>= a2 (+ h 1)) (= ch12 1)))
(assert (=> (< a2 (+ h 1)) (= ch12 0)))
(assert (=> (>= a3 (+ h 1)) (= ch13 1)))
(assert (=> (< a3 (+ h 1)) (= ch13 0)))
(assert (=> (>= a4 (+ h 1)) (= ch14 1)))
(assert (=> (< a4 (+ h 1)) (= ch14 0)))
(assert (< (+ ch10 ch11 ch12 ch13 ch14) (+ h 1)))

; Modified array b (sorted descending, non-negative)
(declare-const b0 Int)
(declare-const b1 Int)
(declare-const b2 Int)
(declare-const b3 Int)
(declare-const b4 Int)

(assert (>= b0 b1))
(assert (>= b1 b2))
(assert (>= b2 b3))
(assert (>= b3 b4))
(assert (>= b4 0))

; b is obtained by incrementing exactly one element of a by 1 (then re-sorting)
; Constraint: sum increases by exactly 1
(assert (= (+ b0 b1 b2 b3 b4) (+ a0 a1 a2 a3 a4 1)))

; For any threshold v, count_ge(b, v) <= count_ge(a, v) + 1
; We need this at v = h+2.
(declare-const cb0 Int)
(declare-const cb1 Int)
(declare-const cb2 Int)
(declare-const cb3 Int)
(declare-const cb4 Int)

(assert (=> (>= b0 (+ h 2)) (= cb0 1)))
(assert (=> (< b0 (+ h 2)) (= cb0 0)))
(assert (=> (>= b1 (+ h 2)) (= cb1 1)))
(assert (=> (< b1 (+ h 2)) (= cb1 0)))
(assert (=> (>= b2 (+ h 2)) (= cb2 1)))
(assert (=> (< b2 (+ h 2)) (= cb2 0)))
(assert (=> (>= b3 (+ h 2)) (= cb3 1)))
(assert (=> (< b3 (+ h 2)) (= cb3 0)))
(assert (=> (>= b4 (+ h 2)) (= cb4 1)))
(assert (=> (< b4 (+ h 2)) (= cb4 0)))

; count_ge(a, h+2)
(declare-const ca0 Int)
(declare-const ca1 Int)
(declare-const ca2 Int)
(declare-const ca3 Int)
(declare-const ca4 Int)

(assert (=> (>= a0 (+ h 2)) (= ca0 1)))
(assert (=> (< a0 (+ h 2)) (= ca0 0)))
(assert (=> (>= a1 (+ h 2)) (= ca1 1)))
(assert (=> (< a1 (+ h 2)) (= ca1 0)))
(assert (=> (>= a2 (+ h 2)) (= ca2 1)))
(assert (=> (< a2 (+ h 2)) (= ca2 0)))
(assert (=> (>= a3 (+ h 2)) (= ca3 1)))
(assert (=> (< a3 (+ h 2)) (= ca3 0)))
(assert (=> (>= a4 (+ h 2)) (= ca4 1)))
(assert (=> (< a4 (+ h 2)) (= ca4 0)))

; Key constraint: count_ge(b, h+2) <= count_ge(a, h+2) + 1
(assert (<= (+ cb0 cb1 cb2 cb3 cb4) (+ ca0 ca1 ca2 ca3 ca4 1)))

; Monotonicity: count_ge(a, h+2) <= count_ge(a, h+1)
(assert (<= (+ ca0 ca1 ca2 ca3 ca4) (+ ch10 ch11 ch12 ch13 ch14)))

; h' is the h-index of b, and we claim h' >= h+2
(declare-const hp Int)
(assert (>= hp (+ h 2)))
(assert (<= hp 5))

; h' satisfies h-index definition: count_ge(b, h') >= h'
; Since h' >= h+2, count_ge(b, h') <= count_ge(b, h+2) (monotonicity)
; So we need count_ge(b, h+2) >= h+2
(assert (>= (+ cb0 cb1 cb2 cb3 cb4) (+ h 2)))

; UNSAT => increment by 1 cannot increase h-index by 2 or more
(check-sat)
