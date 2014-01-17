/*
 * Simple example: build a list with only 1s, then 2s and finally
 * on 3 (arbitrary length); afterwards, go through it and check
 * if the the list does have the correct form, and in particular
 * finishes by a 3.
 */
#include <stdlib.h>
#include "../heap_builtins.h"

void exit(__CPROVER_bool s) {
 _EXIT: goto _EXIT;
}

typedef struct node {
  struct node *h;
  struct node *n;
} *List;

List res, err;

extern __CPROVER_bool nondet();

void main() {
  List one, two, three;
  __CPROVER_assume(one != two);
  __CPROVER_assume(one != three);
  __CPROVER_assume(two != three);

  __CPROVER_assume(res != err);

  /* Build a list of the form 1->...->1->2->....->2->3 */
  List a = (List) malloc(sizeof(struct node));
  if (a == NULL) exit(1);
  List t;
  List p = a;

  while (nondet()) {
    not_null(p);
    p->h = one;
    t = (List) malloc(sizeof(struct node));
    if (t == NULL) exit(1);
    not_null(p);
    p->n = t;
    not_null(p);
    p = p->n;
  }

  while (nondet()) {
    not_null(p);
    p->h = two;
    t = (List) malloc(sizeof(struct node));
    if (t == NULL) exit(1);
    not_null(p);
    p->n = t;
    not_null(p);
    p = p->n;
  }
  not_null(p);
  p->h = three;
    
  /* Check it */
  p = a;

  not_null(p);
  while (p->h == one) {
    not_null(p);
    p = p->n;
    not_null(p);
  }

  //p->h = one; // BUG

  not_null(p);
  while (p->h == two) {
    not_null(p);
    p = p->n;
    // BUG: 
    // p = p->n;
    not_null(p);
  }

  not_null(p);
  if(p->h != three) res = err;
  //ERROR: goto ERROR;

  assert(res!=err);

  //return 0;
}
