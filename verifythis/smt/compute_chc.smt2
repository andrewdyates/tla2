; VerifyThis 2026 Challenge 1: compute() loop invariant verification
; Andrew Yates <andrewyates.name@gmail.com>
; Copyright 2026 Andrew Yates. License: Apache-2.0
;
; C function:
;   int compute(int a[], int n) {
;       int h = 0;
;       while (h < n && h < a[h]) h++;
;       return h;
;   }
;
; Bounded instance: N=5, array elements a0..a4
; Precondition: reverse-sorted non-negative: a0 >= a1 >= a2 >= a3 >= a4 >= 0
;
; Loop invariant: 0 <= h <= 5 AND forall j in [0,h): a[j] >= h
; (which, with sorted array, means: a[h-1] >= h for h>0, plus bounds)
;
; Safety: on exit, h is the h-index:
;   (a) count of elements >= h is at least h  (by invariant: first h elements >= h)
;   (b) NOT (h < 5 AND a[h] > h), i.e., either h=5 or a[h] <= h
;       which means count of elements >= h+1 is at most h (not enough for h+1)

(set-logic HORN)

; Invariant predicate: Inv(h, a0, a1, a2, a3, a4)
; We carry array values through to check safety properties
(declare-fun Inv (Int Int Int Int Int Int) Bool)

; Variables
(declare-var h Int)
(declare-var h1 Int)
(declare-var a0 Int)
(declare-var a1 Int)
(declare-var a2 Int)
(declare-var a3 Int)
(declare-var a4 Int)

; ============================================================
; RULE 1: Initialization
; Precondition: sorted, non-negative. h starts at 0.
; ============================================================
(assert (forall ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (>= a0 a1) (>= a1 a2) (>= a2 a3) (>= a3 a4) (>= a4 0))
      (Inv 0 a0 a1 a2 a3 a4))))

; ============================================================
; RULE 2: Loop step — case split on h for a[h] access
; Guard: h < 5 AND h < a[h]
; Effect: h' = h + 1
; ============================================================

; Case h=0: guard is 0 < 5 AND 0 < a0
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4) (= h 0) (> a0 0))
      (Inv 1 a0 a1 a2 a3 a4))))

; Case h=1: guard is 1 < 5 AND 1 < a1
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4) (= h 1) (> a1 1))
      (Inv 2 a0 a1 a2 a3 a4))))

; Case h=2: guard is 2 < 5 AND 2 < a2
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4) (= h 2) (> a2 2))
      (Inv 3 a0 a1 a2 a3 a4))))

; Case h=3: guard is 3 < 5 AND 3 < a3
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4) (= h 3) (> a3 3))
      (Inv 4 a0 a1 a2 a3 a4))))

; Case h=4: guard is 4 < 5 AND 4 < a4
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4) (= h 4) (> a4 4))
      (Inv 5 a0 a1 a2 a3 a4))))

; ============================================================
; SAFETY QUERY: When loop exits, verify h-index property is WRONG
; (query asks: can we reach a state violating the h-index property?)
;
; Loop exits when: NOT (h < 5 AND h < a[h])
; i.e., h >= 5 OR h >= a[h]
;
; Safety property at exit:
;   For h > 0: a[h-1] >= h  (at least h elements >= h, by sorted)
;   AND (h >= 5 OR a[h] <= h)  (not enough for h+1)
;
; We encode: can we find a state in Inv where the loop exits
; but the h-index property FAILS?
;
; h-index property holds iff:
;   (1) for all j < h: a[j] >= h  (the invariant gives us this)
;   (2) loop exited because h >= 5 or a[h] <= h
;
; The negation we query: Inv holds, loop exits, but
; either (a) some a[j] < h for j < h (invariant violation at exit)
; or     (b) h < 5 AND a[h] > h (loop should not have exited)
;
; Actually, the simplest safety check: the invariant itself is
; inductive and bounds are correct. Check: can Inv(h,...) hold
; with h < 0 or h > 5?
; ============================================================

; Safety check 1: h is always in [0,5]
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4)
           (or (< h 0) (> h 5)))
      false)))

; Safety check 2: at any reachable Inv state, forall j < h: a[j] >= h
; Encode by cases: if h >= 1 then a0 >= h, if h >= 2 then a1 >= h, etc.
(assert (forall ((h Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
  (=> (and (Inv h a0 a1 a2 a3 a4)
           (or (and (>= h 1) (< a0 h))
               (and (>= h 2) (< a1 h))
               (and (>= h 3) (< a2 h))
               (and (>= h 4) (< a3 h))
               (and (>= h 5) (< a4 h))))
      false)))

(check-sat)
(get-model)
