extern int __VERIFIER_nondet_int();
/*
 * Simple example: build a list with only 1s and finally a 0 (arbitrary length); 
 * afterwards, go through it and check if the list does have the correct form, and in particular
 * finishes by a 0.
 */
#include <stdlib.h>
#include "../heap_builtins.h"

extern __CPROVER_bool nondet();

void exit(__CPROVER_bool s) {
	_EXIT: goto _EXIT;
}

typedef struct node {
  struct node * h;
  struct node *n;
} *List;

void main() {
  /* Build a list of the form 1->...->1->0 */

  List zero, one;
  __CPROVER_assume(zero!=one);

  List res, err;
  __CPROVER_assume(res!=err);

  List a = (List) malloc(sizeof(struct node));
  if (a == NULL) exit(1);
  List t;
  List p = a;
  while (nondet()) {
    not_null(p);				
    p->h = one; //BUG zero (this is discovered only from the third unwinding)
    t = (List) malloc(sizeof(struct node));
    if (t == NULL) exit(1);
    not_null(p);				
    p->n = t;
    not_null(p);				
    p = p->n;
 }
  
  not_null(p);				
  p->h = one; //BUG zero (this is discovered from the second unwinding)
  // p = p->n; BUG that i could not find 
  not_null(p);				
  p->n = NULL;
  p = a;
  while (p!=NULL) {
    not_null(p);				
    if (p->h != one) {
      res = err;
      //ERROR: goto ERROR;
    }
    not_null(p);				
    p = p->n;
  }

  assert(res!=err);
}

