#include "../heap_builtins.h"

/* bubble sort */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

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
      if(p == NULL) res=err;
      tmp = p->next;
      tmp = tmp->next;
      //      tmp = tmp->next;
      if(p == NULL) res=err;
      if(tmp == NULL) res=err;
      if(p->value == a && tmp->value == b) {
        if(p == NULL) res=err;
        aux = p->value;
        if(p == NULL) res=err;
        if(tmp == NULL) res=err;
        p->value = tmp->value;
        if(tmp == NULL) res=err;
        tmp->value = aux;
        flag = val1; 
      }
      p = tmp;
    }
  }

  assert(res!=err);
  //  assert(__CPROVER_HEAP_path(p, x, "next"));
}



