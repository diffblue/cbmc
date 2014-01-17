#include "../heap_builtins.h"

/* find */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, tmp;
  list_t a, res, one, zero;

  __CPROVER_assume(one!=zero);

  tmp = x;

  while(tmp != NULL && tmp->value != a) { 
    not_null(tmp);
    tmp = tmp->next;
  }


  if(tmp != NULL)
    res = one;
  else
    res = zero;

  assert(__CPROVER_HEAP_path(x, tmp, "next"));
}



