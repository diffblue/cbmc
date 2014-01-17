#include "../heap_builtins.h"

/* find */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, tmp, res, err;
  list_t a, retval, one, zero;

  __CPROVER_assume(res!=err);
  __CPROVER_assume(one!=zero);

  tmp = x;

  while(/*tmp != NULL &&*/ tmp->value != a) { //Bug: found in one iteration
    not_null(tmp);
    tmp = tmp->next;
  }


  if(tmp != NULL)
    retval = one;
  else
    retval = zero;

  assert(__CPROVER_HEAP_path(x, tmp, "next"));
  assert(res != err);
}



