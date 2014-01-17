/*
 * Odd-Even Splice example: create a list with 1s at odd positions
 * and 2s at even ones. The list is ended by a 3 at the last
 * position.
 * Then, split it into two lists (with only 1s or 2s) and go
 * through those as usual.
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

extern __CPROVER_bool nondet();

void main() {

  List _true, _false;
  __CPROVER_assume(_true != _false);

  List one, two, three;
  __CPROVER_assume(one != two);
  __CPROVER_assume(one != three);
  __CPROVER_assume(two != three);

  List flag = _true;

  List res, err;
  __CPROVER_assume(res != err);
  
  /* Build a list of the form (1->2)*->3 */
  List a = (List) malloc(sizeof(struct node));
  if (a == NULL) exit(1);
  List t;
  List l1;
  List l2;
  List b;
  List u;
  List p = a;
  while (nondet()) {
    if (flag == _true) {
      not_null(p);
      p->h = one;
      flag = _false;
    }
    else {
      not_null(p);
      p->h = two;
      flag = _true;
    }
    t = (List) malloc(sizeof(struct node));
    if (t == NULL) exit(1);
    not_null(p);
    p->n = t;
    not_null(p);
    p = p->n;
  }
  not_null(p);
  p->h = three;

  not_null(a); 
  if (a->h == three) return;

  flag = _true;
  l1 = NULL;
  l2 = NULL;
  p = a;
  not_null(p);
  while (p->h != three) {
    t = p;
    not_null(p);
    p = p->n;
    if (flag == _true) {
      not_null(t);
      //t->n = l1; // BUG (found after 3 unwindings)
      l1 = t; 
      flag = _false;
    } 
    else {
      not_null(t);
      t->n = l2;
      l2 = t; 
      flag = _true;
    }
    not_null(p);
  }
    
  /* Check it */
  p = l1;
  while (p != NULL) {
    not_null(p);
    if (p->h != one) res = err; //goto ERROR;
    not_null(p);
    p = p->n;
  }
  p = l2;
  while (p != NULL) {
    not_null(p);
    if (p->h != two) res = err; //goto ERROR;
    not_null(p);
    p = p->n;
  } 

  //return 0;

  //ERROR: return 1;
  
  assert(res!=err);

}
