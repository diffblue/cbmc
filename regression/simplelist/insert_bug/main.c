#include "../heap_builtins.h"

/* insert */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, y, res, err;
  // value to be inserted
  list_t val;

  __CPROVER_assume(res!=err);

  x = (list_t)malloc(sizeof(struct list));
  not_null(x);
  x->value = val;
  not_null(x);
  // x->next = y; //BUG

  assert(__CPROVER_HEAP_path(x, y, "next"));
  assert(res != err);
}



