/*
 * Simple example: build a list with only 1s and finally a 0 (arbitrary length); 
 * afterwards, go through it and check if the list does have the correct form, and in particular
 * finishes by a 0.
 */
#include <stdlib.h>
#include "../heap_builtins.h"

void exit(__CPROVER_bool s) {
	_EXIT: goto _EXIT;
}

typedef struct node {
  struct node *h; //int
  struct node *n;
} *List;

extern __CPROVER_bool nondet();

void main() {

  List one;
  __CPROVER_assume(one != NULL);

  List res, err;
  __CPROVER_assume(res != err);

  /* Build a list of the form 1->...->1->0 */
  List t;
  List p = NULL;
  while (nondet()) {
    t = (List) malloc(sizeof(struct node));
    if (t == NULL) exit(1);
    not_null(t);
    t->h = one;
    not_null(t);
    t->n = p;
    p = t;
  }
  while (p!=NULL) {
    not_null(p);
    if (p->h != one) res = err; //goto ERROR;
    not_null(p);
    p = p->n; 
  }
  assert(res!=err);
}

