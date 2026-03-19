#include "callback.h"
#include <stdlib.h>

void map_int(int64_t *arr, int n, int64_t (*f)(int64_t)) {
    for (int i = 0; i < n; i++)
        arr[i] = f(arr[i]);
}

int64_t sum_of(int n, int64_t (*f)(int64_t)) {
    int64_t acc = 0;
    for (int i = 0; i < n; i++)
        acc += f((int64_t)i);
    return acc;
}

static int cmp_wrapper_i64(const void *a, const void *b,
                            int (*cmp)(int64_t, int64_t)) {
    return cmp(*(const int64_t *)a, *(const int64_t *)b);
}

int64_t sum_two(int n, int64_t (*f)(int64_t), int64_t (*g)(int64_t)) {
    int64_t acc = 0;
    for (int i = 0; i < n; i++)
        acc += f((int64_t)i) + g((int64_t)i);
    return acc;
}

/* Provide a type-safe qsort for int64_t using a typed comparator. */
void sort_int64(int64_t *arr, int n, int (*cmp)(int64_t, int64_t)) {
    /* simple insertion sort to avoid needing a closure-friendly qsort */
    for (int i = 1; i < n; i++) {
        int64_t key = arr[i];
        int j = i - 1;
        while (j >= 0 && cmp(arr[j], key) > 0) {
            arr[j + 1] = arr[j];
            j--;
        }
        arr[j + 1] = key;
    }
}
