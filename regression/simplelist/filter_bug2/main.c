#include "../heap_builtins.h"

/* filter */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, target;
  list_t aux, a, b;
  list_t res, err;
 
  __CPROVER_assume(res!=err);

  while(x != NULL && x->value == target) {
    aux = x;
    not_null(x);
    x = x->next;
    free(aux); 
  }

  a = x;

  if(x != NULL) {
    not_null(x);
    b = x->next;
  }

  if(x == NULL) {
    b = NULL;    
  }

  while(a != NULL) { //BUG: b replaced by a (found with 2 unwindings)
    not_null(b);
    if(b->value == target) {
      not_null(b);
      aux = b->next;
      not_null(a);
      a->next = aux;
      free(b);
      b = a;
    }
    a = b;
    not_null(b);
    b = b->next;
  } 

  assert(res!=err);
  assert(__CPROVER_HEAP_path(x, a, "next"));
}



