// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// VerifyThis 2026 - Challenge 1: Ada and her papers
// Original C code from the challenge specification
// Author: Andrew Yates <andrewyates.name@gmail.com>

#include <stdio.h>

// given an array 'a' of size 'n', compute its h-index
int compute(int a[], int n) {
    int h = 0;
    while (h < n && h < a[h])
        h++;
    return h;
}

// the same, more efficiently
int compute_opt(int a[], int n) {
    int lo = 0, hi = n;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (a[mid] <= mid) hi = mid;
        else lo = mid + 1;
    }
    return lo;
}

// increments the value at index 'i',
// updates the array and returns the new h-index
int update(int a[], int h, int i) {
    int x = a[i];
    int lo = 0, hi = i;
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        if (a[mid] == x) hi = mid;
        else lo = mid + 1;
    }
    a[lo]++;
    if (lo == h && a[lo] == h+1) return h+1;
    return h;
}
