// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// VerifyThis 2026 - Challenge 1: Bonus task implementations
// Author: Andrew Yates <andrewyates.name@gmail.com>

// B.2: rsorted — Reverse-sorting function (insertion sort, descending)
// Sorts array in reverse (descending) order using insertion sort
void rsorted(int a[], int n) {
    for (int i = 1; i < n; i++) {
        int key = a[i];
        int j = i - 1;
        while (j >= 0 && a[j] < key) {
            a[j + 1] = a[j];
            j--;
        }
        a[j + 1] = key;
    }
}

// Forward declaration of compute_opt from ada.c
int compute_opt(int a[], int n);

// B.3: update_k — Adds k citations to paper i
// Adds k citations to paper at index i, maintains sorted order, returns new h-index
// Precondition: a is reverse-sorted, h is current h-index, 0 <= i < n, k >= 1
int update_k(int a[], int n, int h, int i, int k) {
    (void)h;  // h is not used; we recompute via compute_opt
    int x = a[i];
    int new_val = x + k;

    // Find leftmost position with value x (same binary search as update)
    int lo = 0, hi2 = i;
    while (lo < hi2) {
        int mid = lo + (hi2 - lo) / 2;
        if (a[mid] == x) hi2 = mid;
        else lo = mid + 1;
    }
    // lo is leftmost position with value x

    // Find insertion point for new_val in [0, lo)
    // We need the rightmost position where a[pos] >= new_val
    int lo2 = 0, hi3 = lo;
    while (lo2 < hi3) {
        int mid = lo2 + (hi3 - lo2) / 2;
        if (a[mid] >= new_val) lo2 = mid + 1;
        else hi3 = mid;
    }
    // lo2 is where new_val should go

    // Shift elements [lo2, lo) right by 1
    for (int j = lo; j > lo2; j--) {
        a[j] = a[j - 1];
    }
    a[lo2] = new_val;

    // Recompute h-index using compute_opt (O(log n))
    return compute_opt(a, n);
}
