// This file contains code snippets from "Algorithms in C, Third Edition,
// Parts 1-4," by Robert Sedgewick.
//
// See https://www.cs.princeton.edu/~rs/Algs3.c1-4/code.txt

#include <stdlib.h>
#include <assert.h>

#define N 1000


#ifdef ENABLE_KLEE
#include <klee/klee.h>
#endif

typedef int Key;
typedef int Item;

#define eq(A, B) (!less(A, B) && !less(B, A))
#define key(A) (A)
#define less(A, B) (key(A) < key(B))
#define NULLitem 0

struct STnode;
typedef struct STnode* link;

struct STnode { Item item; link l, r; int n; };
static link head, z;

static link NEW(Item item, link l, link r, int n) {
  link x = malloc(sizeof *x);
  x->item = item; x->l = l; x->r = r; x->n = n;
  return x;
}

void STinit() {
  head = (z = NEW(NULLitem, 0, 0, 0));
}

int STcount() { return head->n; }

static link insertR(link h, Item item) {
  Key v = key(item), t = key(h->item);
  if (h == z) return NEW(item, z, z, 1);

  if (less(v, t))
    h->l = insertR(h->l, item);
  else
    h->r = insertR(h->r, item);

  (h->n)++; return h;
}

void STinsert(Item item) { head = insertR(head, item); }

static void sortR(link h, void (*visit)(Item)) {
  if (h == z) return;
  sortR(h->l, visit);
  visit(h->item);
  sortR(h->r, visit);
}

void STsort(void (*visit)(Item)) { sortR(head, visit); }


static Item a[N];
static unsigned k = 0;
void sorter(Item item) {
  a[k++] = item;
}

#ifdef ENABLE_CPROVER
int nondet_int();
#endif

// Unwind N+1 times
int main() {
#ifdef ENABLE_KLEE
  klee_make_symbolic(a, sizeof(a), "a");
#endif

  STinit();

  for (unsigned i = 0; i < N; i++) {
#ifdef ENABLE_CPROVER
    STinsert(nondet_int());
#elif ENABLE_KLEE
    STinsert(a[i]);
    a[i] = NULLitem;
#endif
  }

  STsort(sorter);

#ifndef FORCE_BRANCH
  for (unsigned i = 0; i < N - 1; i++)
    assert(a[i] <= a[i+1]);
#endif

  return 0;
}
