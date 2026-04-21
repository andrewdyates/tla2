// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// VerifyThis 2026 - Challenge 1: Test harness
// Author: Andrew Yates <andrewyates.name@gmail.com>

#include <stdio.h>
#include <string.h>

// From ada.c
int compute(int a[], int n);
int compute_opt(int a[], int n);
int update(int a[], int h, int i);

// From bonus.c
void rsorted(int a[], int n);
int update_k(int a[], int n, int h, int i, int k);

static int tests_passed = 0;
static int tests_failed = 0;

static void check(const char *name, int condition) {
    if (condition) {
        printf("  PASS: %s\n", name);
        tests_passed++;
    } else {
        printf("  FAIL: %s\n", name);
        tests_failed++;
    }
}

static void print_array(const char *label, int a[], int n) {
    printf("  %s: {", label);
    for (int i = 0; i < n; i++) {
        if (i > 0) printf(", ");
        printf("%d", a[i]);
    }
    printf("}\n");
}

static int arrays_equal(int a[], int b[], int n) {
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

// Test 1: compute and compute_opt on the challenge example
static void test_challenge_example(void) {
    printf("\n--- Test 1: Challenge example array ---\n");
    int a[] = {12, 5, 3, 3, 3, 3, 2, 1, 0, 0};
    int n = 10;

    int h1 = compute(a, n);
    int h2 = compute_opt(a, n);

    printf("  compute    => h = %d\n", h1);
    printf("  compute_opt => h = %d\n", h2);

    check("compute returns 3", h1 == 3);
    check("compute_opt returns 3", h2 == 3);
    check("compute == compute_opt", h1 == h2);
}

// Test 2: update — paper at position 5 gets a citation
static void test_update_no_change(void) {
    printf("\n--- Test 2: update paper at index 5 (h stays 3) ---\n");
    int a[] = {12, 5, 3, 3, 3, 3, 2, 1, 0, 0};
    int n = 10;
    int h = compute(a, n);  // h = 3

    printf("  Before update:\n");
    print_array("a", a, n);
    printf("  h = %d, updating paper at index 5\n", h);

    int new_h = update(a, h, 5);

    printf("  After update:\n");
    print_array("a", a, n);
    printf("  new h = %d\n", new_h);

    // After update(a, 3, 5): a[5]=3, so x=3, leftmost pos with value 3 is index 2.
    // a[2]++ => a[2] becomes 4. Array: {12, 5, 4, 3, 3, 3, 2, 1, 0, 0}
    int expected[] = {12, 5, 4, 3, 3, 3, 2, 1, 0, 0};
    check("array is {12,5,4,3,3,3,2,1,0,0}", arrays_equal(a, expected, n));
    check("h-index stays 3", new_h == 3);
    check("compute confirms h=3", compute(a, n) == 3);
}

// Test 3: update — paper at position 4 gets a citation (h increases to 4)
static void test_update_h_increases(void) {
    printf("\n--- Test 3: update paper at index 4 (h increases to 4) ---\n");
    // Start from the array after Test 2: {12, 5, 4, 3, 3, 3, 2, 1, 0, 0}
    int a[] = {12, 5, 4, 3, 3, 3, 2, 1, 0, 0};
    int n = 10;
    int h = 3;

    printf("  Before update:\n");
    print_array("a", a, n);
    printf("  h = %d, updating paper at index 4\n", h);

    int new_h = update(a, h, 4);

    printf("  After update:\n");
    print_array("a", a, n);
    printf("  new h = %d\n", new_h);

    // update(a, 3, 4): a[4]=3, x=3. Leftmost pos with value 3 is index 3.
    // a[3]++ => a[3] becomes 4. Array: {12, 5, 4, 4, 3, 3, 2, 1, 0, 0}
    // lo=3 == h=3 and a[3]=4 == h+1=4, so return h+1=4
    int expected[] = {12, 5, 4, 4, 3, 3, 2, 1, 0, 0};
    check("array is {12,5,4,4,3,3,2,1,0,0}", arrays_equal(a, expected, n));
    check("h-index increases to 4", new_h == 4);
    check("compute confirms h=4", compute(a, n) == 4);
}

// Test 4: rsorted on unsorted input
static void test_rsorted(void) {
    printf("\n--- Test 4: rsorted on unsorted input ---\n");
    int a[] = {3, 1, 4, 1, 5, 9, 2, 6};
    int n = 8;

    printf("  Before rsorted:\n");
    print_array("a", a, n);

    rsorted(a, n);

    printf("  After rsorted:\n");
    print_array("a", a, n);

    int expected[] = {9, 6, 5, 4, 3, 2, 1, 1};
    check("rsorted produces descending order", arrays_equal(a, expected, n));

    // Verify descending property
    int is_desc = 1;
    for (int i = 0; i + 1 < n; i++) {
        if (a[i] < a[i + 1]) { is_desc = 0; break; }
    }
    check("result is reverse-sorted (a[i] >= a[i+1])", is_desc);
}

// Test 4b: rsorted on already sorted, empty, single element
static void test_rsorted_edge_cases(void) {
    printf("\n--- Test 4b: rsorted edge cases ---\n");

    // Already reverse-sorted
    int a1[] = {5, 4, 3, 2, 1};
    rsorted(a1, 5);
    int exp1[] = {5, 4, 3, 2, 1};
    check("already sorted stays same", arrays_equal(a1, exp1, 5));

    // Single element
    int a2[] = {42};
    rsorted(a2, 1);
    check("single element unchanged", a2[0] == 42);

    // All same values
    int a3[] = {3, 3, 3, 3};
    rsorted(a3, 4);
    int exp3[] = {3, 3, 3, 3};
    check("all-same array unchanged", arrays_equal(a3, exp3, 4));

    // Ascending to descending
    int a4[] = {1, 2, 3, 4, 5};
    rsorted(a4, 5);
    int exp4[] = {5, 4, 3, 2, 1};
    check("ascending reversed to descending", arrays_equal(a4, exp4, 5));
}

// Test 5: update_k with k=3
static void test_update_k(void) {
    printf("\n--- Test 5: update_k with k=3 ---\n");
    int a[] = {12, 5, 3, 3, 3, 3, 2, 1, 0, 0};
    int n = 10;
    int h = compute(a, n);  // h = 3

    printf("  Before update_k:\n");
    print_array("a", a, n);
    printf("  h = %d, adding k=3 citations to paper at index 7\n", h);

    int new_h = update_k(a, n, h, 7, 3);

    printf("  After update_k:\n");
    print_array("a", a, n);
    printf("  new h = %d\n", new_h);

    // Paper at index 7 has value 1, adding 3 gives 4.
    // Need to insert 4 into the right position.
    // Expected: {12, 5, 4, 3, 3, 3, 2, 0, 0, ...} - 4 moves up
    check("h-index correct after update_k", new_h == compute(a, n));
    int is_desc = 1;
    for (int i = 0; i + 1 < n; i++) {
        if (a[i] < a[i + 1]) { is_desc = 0; break; }
    }
    check("result is reverse-sorted after update_k", is_desc);
}

// Test 5b: update_k that increases h-index
static void test_update_k_h_increases(void) {
    printf("\n--- Test 5b: update_k that increases h-index ---\n");
    // Array where h=2, adding enough to push h up
    int a[] = {5, 3, 1, 0, 0};
    int n = 5;
    int h = compute(a, n);
    printf("  Initial h = %d\n", h);
    check("initial h = 2", h == 2);

    print_array("before", a, n);
    // Add 4 to paper at index 2 (value 1 -> 5)
    int new_h = update_k(a, n, h, 2, 4);
    print_array("after", a, n);
    printf("  new h = %d\n", new_h);

    check("h increased to 3", new_h == 3);
    check("compute confirms", compute(a, n) == new_h);

    int is_desc = 1;
    for (int i = 0; i + 1 < n; i++) {
        if (a[i] < a[i + 1]) { is_desc = 0; break; }
    }
    check("result is reverse-sorted", is_desc);
}

// Test 6: compute == compute_opt on various arrays
static void test_compute_consistency(void) {
    printf("\n--- Test 6: compute == compute_opt consistency ---\n");

    int test_arrays[][10] = {
        {10, 8, 5, 4, 3, 3, 2, 1, 0, 0},  // h=4
        {0, 0, 0, 0, 0, 0, 0, 0, 0, 0},    // h=0
        {9, 9, 9, 9, 9, 9, 9, 9, 9, 9},    // h=9 (all >= their index, but n=10 so h=9)
        {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},    // h=1
        {5, 5, 5, 5, 5, 0, 0, 0, 0, 0},    // h=5
    };
    int sizes[] = {10, 10, 10, 10, 10};
    int expected_h[] = {4, 0, 9, 1, 5};
    int n_tests = 5;

    int all_ok = 1;
    for (int t = 0; t < n_tests; t++) {
        int h1 = compute(test_arrays[t], sizes[t]);
        int h2 = compute_opt(test_arrays[t], sizes[t]);
        if (h1 != h2) {
            printf("  MISMATCH on test %d: compute=%d, compute_opt=%d\n", t, h1, h2);
            all_ok = 0;
        }
        if (h1 != expected_h[t]) {
            printf("  WRONG h on test %d: got %d, expected %d\n", t, h1, expected_h[t]);
            all_ok = 0;
        }
    }
    check("all hand-crafted arrays: compute == compute_opt", all_ok);
}

// Test 7: Exhaustive test — ALL reverse-sorted arrays of size 4 with values 0..6
static void test_exhaustive(void) {
    printf("\n--- Test 7: Exhaustive test (size 4, values 0..6) ---\n");

    int count = 0;
    int mismatches = 0;

    // Enumerate all reverse-sorted arrays: a[0] >= a[1] >= a[2] >= a[3], each in 0..6
    for (int a0 = 0; a0 <= 6; a0++) {
        for (int a1 = 0; a1 <= a0; a1++) {
            for (int a2 = 0; a2 <= a1; a2++) {
                for (int a3 = 0; a3 <= a2; a3++) {
                    int a[] = {a0, a1, a2, a3};
                    int h1 = compute(a, 4);
                    int h2 = compute_opt(a, 4);
                    count++;
                    if (h1 != h2) {
                        if (mismatches < 5) {
                            printf("  MISMATCH: {%d,%d,%d,%d} => compute=%d, compute_opt=%d\n",
                                   a0, a1, a2, a3, h1, h2);
                        }
                        mismatches++;
                    }
                }
            }
        }
    }

    printf("  Tested %d reverse-sorted arrays\n", count);
    printf("  Mismatches: %d\n", mismatches);
    check("all reverse-sorted arrays: compute == compute_opt", mismatches == 0);
    check("tested a meaningful number of arrays (>100)", count > 100);
}

// Test 8: Exhaustive update test — verify update returns correct h-index
static void test_exhaustive_update(void) {
    printf("\n--- Test 8: Exhaustive update test (size 4, values 0..5) ---\n");

    int count = 0;
    int failures = 0;

    for (int a0 = 0; a0 <= 5; a0++) {
        for (int a1 = 0; a1 <= a0; a1++) {
            for (int a2 = 0; a2 <= a1; a2++) {
                for (int a3 = 0; a3 <= a2; a3++) {
                    int h = compute((int[]){a0, a1, a2, a3}, 4);
                    // Try updating each position
                    for (int i = 0; i < 4; i++) {
                        int a[] = {a0, a1, a2, a3};
                        int new_h = update(a, h, i);
                        int actual_h = compute(a, 4);
                        count++;
                        if (new_h != actual_h) {
                            if (failures < 5) {
                                printf("  FAIL: {%d,%d,%d,%d} update(%d): returned h=%d, actual h=%d\n",
                                       a0, a1, a2, a3, i, new_h, actual_h);
                                print_array("  resulting array", a, 4);
                            }
                            failures++;
                        }
                    }
                }
            }
        }
    }

    printf("  Tested %d update operations\n", count);
    printf("  Failures: %d\n", failures);
    check("all update operations return correct h-index", failures == 0);
}

// Test 9: rsorted + compute consistency
static void test_rsorted_compute(void) {
    printf("\n--- Test 9: rsorted then compute on unsorted arrays ---\n");

    // Various unsorted arrays, sort them, verify compute works
    int a1[] = {0, 3, 1, 5, 2};
    rsorted(a1, 5);
    int h1 = compute(a1, 5);
    int h1_opt = compute_opt(a1, 5);
    check("sorted {0,3,1,5,2}: compute == compute_opt", h1 == h1_opt);
    check("sorted {0,3,1,5,2}: h=2", h1 == 2);

    int a2[] = {10, 10, 10, 10, 10};
    rsorted(a2, 5);
    int h2 = compute(a2, 5);
    check("sorted {10,10,10,10,10}: h=5", h2 == 5);
}

// Test 10: Empty and small arrays
static void test_edge_cases(void) {
    printf("\n--- Test 10: Edge cases ---\n");

    // Empty array
    int h_empty = compute((int[]){}, 0);
    int h_empty_opt = compute_opt((int[]){}, 0);
    check("empty array: compute=0", h_empty == 0);
    check("empty array: compute_opt=0", h_empty_opt == 0);

    // Single element 0
    int h_zero = compute((int[]){0}, 1);
    check("single [0]: h=0", h_zero == 0);

    // Single element 1
    int h_one = compute((int[]){1}, 1);
    check("single [1]: h=1", h_one == 1);

    // Single element 100
    int h_big = compute((int[]){100}, 1);
    check("single [100]: h=1", h_big == 1);

    // Two elements
    int h_two = compute((int[]){3, 2}, 2);
    check("[3,2]: h=2", h_two == 2);

    int h_two2 = compute((int[]){1, 0}, 2);
    check("[1,0]: h=1", h_two2 == 1);
}

int main(void) {
    printf("=== VerifyThis 2026 Challenge 1: Test Harness ===\n");

    test_challenge_example();
    test_update_no_change();
    test_update_h_increases();
    test_rsorted();
    test_rsorted_edge_cases();
    test_update_k();
    test_update_k_h_increases();
    test_compute_consistency();
    test_exhaustive();
    test_exhaustive_update();
    test_rsorted_compute();
    test_edge_cases();

    printf("\n=== Summary: %d passed, %d failed ===\n", tests_passed, tests_failed);
    if (tests_failed == 0) {
        printf("ALL TESTS PASSED\n");
        return 0;
    } else {
        printf("SOME TESTS FAILED\n");
        return 1;
    }
}
