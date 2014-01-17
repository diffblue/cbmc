#include "../heap_builtins.h"

/* create */

/* expect bottom */

struct list {
  int value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, y, tmp, val1, val2, count;
  list_t aux;

  __CPROVER_assume(val1!=val2);

  x = (struct list*)malloc(sizeof(struct list));
  not_null(x);
  x->next = NULL;

  tmp = x;

  while(count == val1) {
    aux = (struct list*)malloc(sizeof(struct list));
    not_null(tmp);
    tmp->next = NULL; //aux; BUG: found with 2 unwindings
    tmp = tmp->next;	  
    count = val2;
  }

  not_null(tmp);
  tmp->next = NULL;

  assert(__CPROVER_HEAP_path(x, NULL, "next"));
}



