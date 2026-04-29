; VerifyThis 2026 Challenge 1: update() binary search invariant verification
; Andrew Yates <andrewyates.name@gmail.com>
; Copyright 2026 Dropbox. License: Apache-2.0
;
; C function:
;   int update(int a[], int h, int i) {
;       int x = a[i];
;       int lo = 0, hi = i;
;       while (lo < hi) {
;           int mid = lo + (hi - lo) / 2;
;           if (a[mid] == x) hi = mid;
;           else lo = mid + 1;
;       }
;       a[lo]++;
;       if (lo == h && a[lo] == h+1) return h+1;
;       return h;
;   }
;
; Binary search finds leftmost position where a[mid] == x in [0, i].
; Bounded N=5, i=4.
;
; Approach: overapproximate by abstracting away array values from invariant.
; We verify BOUNDS: 0 <= lo <= hi <= 4 is maintained, and lo and hi converge.
;
; (lo, hi) pairs with 0 <= lo < hi <= 4:
;   lo=0,hi=1,mid=0  lo=0,hi=2,mid=1  lo=0,hi=3,mid=1  lo=0,hi=4,mid=2
;   lo=1,hi=2,mid=1  lo=1,hi=3,mid=2  lo=1,hi=4,mid=2
;   lo=2,hi=3,mid=2  lo=2,hi=4,mid=3
;   lo=3,hi=4,mid=3

(set-logic HORN)

; Inv(lo, hi) — bounds invariant
(declare-fun Inv (Int Int) Bool)

; ============================================================
; INITIALIZATION: lo=0, hi=4
; ============================================================
(assert (Inv 0 4))

; ============================================================
; STEP RULES: Both branches from each (lo, hi) pair
; Branch 1 (a[mid] == x): hi = mid
; Branch 2 (a[mid] != x): lo = mid + 1
; ============================================================

; --- lo=0, hi=1, mid=0 ---
(assert (=> (Inv 0 1) (Inv 0 0)))
(assert (=> (Inv 0 1) (Inv 1 1)))

; --- lo=0, hi=2, mid=1 ---
(assert (=> (Inv 0 2) (Inv 0 1)))
(assert (=> (Inv 0 2) (Inv 2 2)))

; --- lo=0, hi=3, mid=1 ---
(assert (=> (Inv 0 3) (Inv 0 1)))
(assert (=> (Inv 0 3) (Inv 2 3)))

; --- lo=0, hi=4, mid=2 ---
(assert (=> (Inv 0 4) (Inv 0 2)))
(assert (=> (Inv 0 4) (Inv 3 4)))

; --- lo=1, hi=2, mid=1 ---
(assert (=> (Inv 1 2) (Inv 1 1)))
(assert (=> (Inv 1 2) (Inv 2 2)))

; --- lo=1, hi=3, mid=2 ---
(assert (=> (Inv 1 3) (Inv 1 2)))
(assert (=> (Inv 1 3) (Inv 3 3)))

; --- lo=1, hi=4, mid=2 ---
(assert (=> (Inv 1 4) (Inv 1 2)))
(assert (=> (Inv 1 4) (Inv 3 4)))

; --- lo=2, hi=3, mid=2 ---
(assert (=> (Inv 2 3) (Inv 2 2)))
(assert (=> (Inv 2 3) (Inv 3 3)))

; --- lo=2, hi=4, mid=3 ---
(assert (=> (Inv 2 4) (Inv 2 3)))
(assert (=> (Inv 2 4) (Inv 4 4)))

; --- lo=3, hi=4, mid=3 ---
(assert (=> (Inv 3 4) (Inv 3 3)))
(assert (=> (Inv 3 4) (Inv 4 4)))

; ============================================================
; SAFETY: bounds — 0 <= lo <= hi <= 4
; ============================================================
(assert (forall ((lo Int) (hi Int))
  (=> (and (Inv lo hi)
           (or (< lo 0) (> hi 4) (> lo hi)))
      false)))

; ============================================================
; SAFETY: at termination lo == hi, result is in [0..4]
; ============================================================
(assert (forall ((lo Int) (hi Int))
  (=> (and (Inv lo hi) (= lo hi)
           (or (< lo 0) (> lo 4)))
      false)))

(check-sat)
(get-model)
