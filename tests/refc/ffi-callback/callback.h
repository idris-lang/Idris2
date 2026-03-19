#pragma once
#include <stdint.h>

/* Apply f to each element of arr in-place. */
void map_int(int64_t *arr, int n, int64_t (*f)(int64_t));

/* Return the sum produced by calling f(i) for i in [0, n). */
int64_t sum_of(int n, int64_t (*f)(int64_t));

/* qsort wrapper for int64_t arrays. */
void sort_int64(int64_t *arr, int n, int (*cmp)(int64_t, int64_t));

/* Call f(i) and g(i) for i in [0, n); return sum of f(i) + g(i). */
int64_t sum_two(int n, int64_t (*f)(int64_t), int64_t (*g)(int64_t));
