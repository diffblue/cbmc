/*
 * Variation on example 0: use a (non-deterministic) boolean
 * flag to set the value of the elements in the list before
 * 3 to a value depending on the flag, and check later on
 * that the list is what has been built just before.
 */
#include <stdlib.h>
/*  #include "assert.h" */

void exit(__CPROVER_bool s) {
 _EXIT: goto _EXIT;
}

typedef struct node {
  struct node *h;
  struct node *n;
} *List;


#define not_null(x) if(x == NULL) res = err;

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

  List res, err;
  __CPROVER_assume(res != err);

  __CPROVER_assume(flag == _true);

    a = (List) malloc(sizeof(struct node));
    p = a;

    if (flag == _true) {
      p->h = one;
    }
    if (flag == _false) {
      p->h = two;
    }
    p = p->n;
    p->h = three;
    
  p = a;
  if (flag == _true) {
    if (p->h == one) {
      p = p->n;
    }
  }
  if (flag == _false) {
    if (p->h == two) {
         p = p->n;
    }
  }

  if (p->h != three) res = err;

  assert(res != err);


}
