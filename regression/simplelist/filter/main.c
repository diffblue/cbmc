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

  while(x != NULL && x->value == target) {
    aux = x;
    assert(x != NULL);
    x = x->next;
    free(aux); 
  }

  a = x;

  if(x != NULL) {
    assert(x != NULL);
    b = x->next;
  }

  if(x == NULL) {
    b = NULL;    
  }

  while(b != NULL) {
    assert(b != NULL);
    if(b->value == target) {
      assert(b != NULL);
      aux = b->next;
      assert(a != NULL);
      a->next = aux;
      free(b);
      b = a;
    }
    a = b;
    assert(b != NULL);
    b = b->next;
  } 

  assert(__CPROVER_HEAP_path(x, a, "next"));
}



