#include "../heap_builtins.h"

/* bubble sort */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

#define not_null(x) if(x == NULL) res = err;

void main() {
  list_t x, p, tmp;
  list_t val1, val2;
  list_t a, b;
  list_t aux, flag;
  list_t res, err;

  __CPROVER_assume(val1!=val2);
  __CPROVER_assume(a!=b);
  __CPROVER_assume(res!=err);

  p = x;

  while(flag == val1) { 
    flag = val2;
  
    p = x;
    while(p != NULL &&  p->next != NULL) {
      not_null(p);
      tmp = p->next;
      not_null(p);
      not_null(tmp);
      if(p->value == a && tmp->value == b) {
        not_null(p);
        aux = p->value;
        not_null(p);
        not_null(tmp);
        p->value = tmp->value;
        not_null(tmp);
        tmp->value = aux;
        flag = val1; 
      }
      p = tmp;
    }
  }

  assert(res!=err);
  //  assert(__CPROVER_HEAP_path(p, x, "next"));
}



