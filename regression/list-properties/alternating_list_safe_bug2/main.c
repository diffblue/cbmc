extern int __VERIFIER_nondet_int();
/*
 * Alternating list example: 
 * creats a list with 1s at odd positions and 2s at even ones. 
 * Then, it goes through and checks if the alternation holds.
 */
#include <stdlib.h>

typedef struct node {
  struct node *h; //int
  struct node *n;
} *List;

void exit(__CPROVER_bool s) {
	_EXIT: goto _EXIT;
}

#define not_null(x) ; //if(x == NULL) res = err;

extern __CPROVER_bool nondet();

int main() {
  List _true, _false;
  __CPROVER_assume(_false == NULL);
  __CPROVER_assume(_true != _false);

  List one, two, three;
  __CPROVER_assume(one == NULL);
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
    p->h = two; //BUG: all two
    p = p->n;
  }
  not_null(p);
  p->h = three;

  /* Check it */
  p = a;
  flag = _true;
  not_null(p);
  while (p->h != three) {
    if (flag == _true) {
      flag = _false;
      not_null(p);
      if (p->h != one) res = err; //goto ERROR;
    } else {
      flag = _true;
      not_null(p);
      if (p->h != two) res = err; //goto ERROR;
    }
    not_null(p);
    p = p->n;
  }

  //return 0;

  //  ERROR:
  //    printf("Alternation violation found.\n");
  //   return 1;
  
  assert(res!=err);
}
