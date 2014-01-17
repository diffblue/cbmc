/*
 * Variation on example 0: use a (non-deterministic) boolean
 * flag to set the value of the elements in the list before
 * 3 to a value depending on the flag, and check later on
 * that the list is what has been built just before.
 */
#include <stdlib.h>
/*  #include "assert.h" */
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
  int flag;
  List p, a, t;

  List _true, _false;
  __CPROVER_assume(_true != _false);

  List one, two, three;
  __CPROVER_assume(one != two);
  __CPROVER_assume(one != three);
  __CPROVER_assume(two != three);

  __CPROVER_assume(res != err);


  /* Build a list of the form x->x->x->...->x->3
   * with x depending on some flag
   */
    a = (List) malloc(sizeof(struct node));
    if (a == NULL) exit(1);
 
 p = a;

  while (nondet()) { 
    if (flag == _true) {
      not_null(p);
      p->h = one;
    } 
    else {
      not_null(p);
      p->h = two;
      p = p->n; //BUG: (found after two unwindings)
    }
    t = (List) malloc(sizeof(struct node));
    if (t == NULL) exit(1);
    not_null(p);
    p->n = t;
    not_null(p);
    p = p->n;
  }
  //p = p->n; //BUG: (found after one unwinding)
  not_null(p);
  p->h = three;
    
  p = a;
  if (flag == _true) {
    not_null(p);
    while (p->h == one) { 
      not_null(p);
      p = p->n;
      not_null(p);
    }
  }
  else {
    while (p->h == two) {
      not_null(p);
      p = p->n;
      not_null(p);
    }
  }

not_null(p);
  if (p->h != three) res = err;
  //ERROR: goto ERROR;

  assert(res != err);

}
