#include "../heap_builtins.h"

/* traverse */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, p, res, err;

  __CPROVER_assume(res!=err);

  p = x;

  while(p != NULL) {
    not_null(p);
    p = p->next;
  }

  assert(__CPROVER_HEAP_path(x, NULL, "next"));
  assert(res != err);
}



