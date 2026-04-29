--------------------------- MODULE HIndex ---------------------------
\* TLA+ specification for VerifyThis 2026 Challenge 1: H-Index.
\*
\* Models three C functions on a reverse-sorted array of non-negative
\* integers as state machines with explicit program counters:
\*   - compute:     linear scan O(n)
\*   - compute_opt: binary search O(log n)
\*   - update:      increment element, maintain sorted order, return new h
\*
\* Each function is modeled as a separate specification (Init/Next pair)
\* with nondeterministic initial array selection over all reverse-sorted
\* arrays of length N with values in 0..MaxVal.
\*
\* Author: Andrew Yates <andrewyates.name@gmail.com>
\* Copyright 2026 Dropbox. | Apache 2.0

EXTENDS Integers, FiniteSets

CONSTANTS N,       \* Array length (>= 1)
          MaxVal   \* Maximum array element value

\* Domain of the array
Dom == 0..(N-1)

\* Range of array element values
Vals == 0..MaxVal

------------------------------------------------------------------------
\* Helper predicates
------------------------------------------------------------------------

\* Reverse-sorted (non-increasing) predicate for a function arr: Dom -> Vals
RevSorted(arr, n) ==
    \A i \in 0..(n-2) : arr[i] >= arr[i+1]

\* Count of elements >= v in arr[0..n-1]
CountGE(arr, n, v) ==
    Cardinality({i \in 0..(n-1) : arr[i] >= v})

\* The h-index of arr is the largest h in 0..n such that at least h
\* elements are >= h. Equivalently: CountGE(arr,n,h) >= h and either
\* h = n or CountGE(arr,n,h+1) < h+1.
IsHIndex(arr, n, h) ==
    /\ h \in 0..n
    /\ CountGE(arr, n, h) >= h
    /\ \/ h = n
       \/ CountGE(arr, n, h + 1) < h + 1

\* Unique h-index value for a given array (used in Init for update)
HIndexOf(arr, n) == CHOOSE h \in 0..n : IsHIndex(arr, n, h)

\* Set of all reverse-sorted arrays of length N with values in Vals
SortedArrays == {f \in [Dom -> Vals] : RevSorted(f, N)}

------------------------------------------------------------------------
\* Variables
------------------------------------------------------------------------

VARIABLES
    a,       \* The array: function Dom -> Vals
    pc,      \* Program counter: "init", "loop", "bsearch", "done"
    mode,    \* Which function: "compute", "compute_opt", "update"
    h,       \* h variable (compute result / update parameter)
    lo,      \* Binary search lo bound
    hi,      \* Binary search hi bound
    mid,     \* Binary search midpoint
    x,       \* Saved value a[idx] for update
    idx,     \* Index parameter for update
    result,  \* Return value
    old_a    \* Saved initial array for postcondition checking

vars == <<a, pc, mode, h, lo, hi, mid, x, idx, result, old_a>>

------------------------------------------------------------------------
\* Task 1: compute (linear scan)
\*
\*   int compute(int a[], int n) {
\*       int h = 0;
\*       while (h < n && h < a[h]) h++;
\*       return h;
\*   }
------------------------------------------------------------------------

ComputeInit ==
    /\ a \in SortedArrays
    /\ pc = "loop"
    /\ mode = "compute"
    /\ h = 0
    /\ lo = 0
    /\ hi = 0
    /\ mid = 0
    /\ x = 0
    /\ idx = 0
    /\ result = -1
    /\ old_a = a

\* One iteration of the compute loop
ComputeStep ==
    /\ mode = "compute"
    /\ pc = "loop"
    /\ IF h < N
       THEN IF h < a[h]
            THEN /\ h' = h + 1
                 /\ pc' = "loop"
                 /\ result' = result
            ELSE /\ result' = h
                 /\ pc' = "done"
                 /\ h' = h
       ELSE /\ result' = h
            /\ pc' = "done"
            /\ h' = h
    /\ UNCHANGED <<a, mode, lo, hi, mid, x, idx, old_a>>

ComputeNext == ComputeStep

ComputeSpec == ComputeInit /\ [][ComputeNext]_vars

------------------------------------------------------------------------
\* Task 2: compute_opt (binary search)
\*
\*   int compute_opt(int a[], int n) {
\*       int lo = 0, hi = n;
\*       while (lo < hi) {
\*           int mid = lo + (hi - lo) / 2;
\*           if (a[mid] <= mid) hi = mid;
\*           else lo = mid + 1;
\*       }
\*       return lo;
\*   }
\*
\* Key insight: for a reverse-sorted array, a[i] > i iff the h-index
\* is > i. The binary search finds the smallest i where a[i] <= i.
------------------------------------------------------------------------

ComputeOptInit ==
    /\ a \in SortedArrays
    /\ pc = "loop"
    /\ mode = "compute_opt"
    /\ h = 0
    /\ lo = 0
    /\ hi = N
    /\ mid = 0
    /\ x = 0
    /\ idx = 0
    /\ result = -1
    /\ old_a = a

\* One iteration of the compute_opt loop
ComputeOptStep ==
    /\ mode = "compute_opt"
    /\ pc = "loop"
    /\ IF lo < hi
       THEN LET m == lo + (hi - lo) \div 2
            IN /\ mid' = m
               /\ IF a[m] <= m
                  THEN /\ hi' = m
                       /\ lo' = lo
                  ELSE /\ lo' = m + 1
                       /\ hi' = hi
               /\ pc' = "loop"
               /\ result' = result
       ELSE /\ result' = lo
            /\ pc' = "done"
            /\ UNCHANGED <<lo, hi, mid>>
    /\ UNCHANGED <<a, mode, h, x, idx, old_a>>

ComputeOptNext == ComputeOptStep

ComputeOptSpec == ComputeOptInit /\ [][ComputeOptNext]_vars

------------------------------------------------------------------------
\* Task 3: update (increment and adjust h-index)
\*
\*   int update(int a[], int h, int i) {
\*       int x = a[i];
\*       int lo = 0, hi = i;
\*       while (lo < hi) {
\*           int mid = lo + (hi - lo) / 2;
\*           if (a[mid] == x) hi = mid;
\*           else lo = mid + 1;
\*       }
\*       a[lo]++;
\*       if (lo == h && a[lo] == h+1) return h+1;
\*       return h;
\*   }
\*
\* Precondition: a is reverse-sorted, h = HIndexOf(a, N).
\* The function finds the leftmost position with value x = a[i],
\* increments that position to maintain sort order, and returns
\* the (possibly incremented) h-index.
------------------------------------------------------------------------

UpdateInit ==
    /\ a \in SortedArrays
    /\ idx \in Dom
    /\ h = HIndexOf(a, N)
    /\ x = a[idx]
    /\ lo = 0
    /\ hi = idx
    /\ pc = "loop"
    /\ mode = "update"
    /\ mid = 0
    /\ result = -1
    /\ old_a = a

\* Binary search loop: find leftmost position with value x
UpdateSearchStep ==
    /\ mode = "update"
    /\ pc = "loop"
    /\ IF lo < hi
       THEN LET m == lo + (hi - lo) \div 2
            IN /\ mid' = m
               /\ IF a[m] = x
                  THEN /\ hi' = m
                       /\ lo' = lo
                  ELSE /\ lo' = m + 1
                       /\ hi' = hi
               /\ pc' = "loop"
               /\ UNCHANGED <<a, result>>
       ELSE \* Search done: perform the increment and compute result
            LET newA == [a EXCEPT ![lo] = a[lo] + 1]
            IN /\ a' = newA
               /\ IF lo = h /\ a[lo] + 1 = h + 1
                  THEN result' = h + 1
                  ELSE result' = h
               /\ pc' = "done"
               /\ UNCHANGED <<lo, hi, mid>>
    /\ UNCHANGED <<mode, h, x, idx, old_a>>

UpdateNext == UpdateSearchStep

UpdateSpec == UpdateInit /\ [][UpdateNext]_vars

------------------------------------------------------------------------
\* Combined specification: nondeterministically choose which function
\* to model-check
------------------------------------------------------------------------

Init == ComputeInit \/ ComputeOptInit \/ UpdateInit

Next == ComputeNext \/ ComputeOptNext \/ UpdateNext

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
\* Type invariant
------------------------------------------------------------------------

TypeOK ==
    /\ a \in [Dom -> 0..(MaxVal + 1)]  \* +1 for update increment
    /\ pc \in {"loop", "done"}
    /\ mode \in {"compute", "compute_opt", "update"}
    /\ h \in 0..N
    /\ lo \in 0..N
    /\ hi \in 0..N
    /\ mid \in 0..N
    /\ x \in Vals
    /\ idx \in Dom
    /\ result \in (-1)..N
    /\ old_a \in [Dom -> Vals]

------------------------------------------------------------------------
\* Loop invariants
------------------------------------------------------------------------

\* compute: all elements before h satisfy a[j] >= h, and h is in range
ComputeInvariant ==
    mode = "compute" /\ pc = "loop" =>
        /\ h \in 0..N
        /\ \A j \in 0..(h-1) : a[j] >= h

\* compute_opt: the answer lies in [lo, hi], with boundary properties
\* - All indices j in 0..(lo-1) have a[j] > j (h-index is > j)
\* - All indices j in hi..(N-1) have a[j] <= j (h-index is <= j)
ComputeOptInvariant ==
    mode = "compute_opt" /\ pc = "loop" =>
        /\ 0 <= lo /\ lo <= hi /\ hi <= N
        /\ \A j \in 0..(lo-1) : a[j] > j
        /\ \A j \in hi..(N-1) : a[j] <= j

\* update: binary search maintains that leftmost x is in [lo, hi]
UpdateSearchInvariant ==
    mode = "update" /\ pc = "loop" =>
        /\ 0 <= lo /\ lo <= hi /\ hi <= idx
        /\ \A j \in 0..(lo-1) : a[j] # x

------------------------------------------------------------------------
\* Correctness properties (postconditions)
------------------------------------------------------------------------

\* When compute finishes, result equals the h-index
ComputeCorrect ==
    mode = "compute" /\ pc = "done" =>
        IsHIndex(old_a, N, result)

\* When compute_opt finishes, result equals the h-index
ComputeOptCorrect ==
    mode = "compute_opt" /\ pc = "done" =>
        IsHIndex(old_a, N, result)

\* When update finishes, the array is still reverse-sorted
UpdatePreservesSorted ==
    mode = "update" /\ pc = "done" =>
        RevSorted(a, N)

\* When update finishes, result is the h-index of the new array
UpdateCorrect ==
    mode = "update" /\ pc = "done" =>
        IsHIndex(a, N, result)

=============================================================================
