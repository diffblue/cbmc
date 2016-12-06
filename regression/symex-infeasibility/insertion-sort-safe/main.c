// This file contains code snippets from "Algorithms in C, Third Edition,
// Parts 1-4," by Robert Sedgewick.
//
// See https://www.cs.princeton.edu/~rs/Algs3.c1-4/code.txt

#include <assert.h>

#define N 5

#ifdef ENABLE_KLEE
#include <klee/klee.h>
#endif

typedef int Item;
#define key(A) (A)
#define less(A, B) (key(A) < key(B))
#define exch(A, B) { Item t = A; A = B; B = t; }
#define compexch(A, B) if (less(B, A)) exch(A, B)

void insertion_sort(Item a[], int l, int r) {
  int i;
  for (i = l+1; i <= r; i++) compexch(a[l], a[i]);
  for (i = l+2; i <= r; i++) {
    int j = i; Item v = a[i];
    while (0 < j && less(v, a[j-1])) {
      a[j] = a[j-1]; j--;
    }
    a[j] = v;
  }
}

int main() {
  int a[N];

#ifdef ENABLE_KLEE
  klee_make_symbolic(a, sizeof(a), "a");
#endif

#ifndef FORCE_BRANCH
  insertion_sort(a, 0, N-1);
  for (unsigned i = 0; i < N - 1; i++)
    assert(a[i] <= a[i+1]);
#endif

  return 0;
}
