#include "../heap_builtins.h"

/* traverse */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, p;

  p = x;

  while(p != NULL) {
    assert(p != NULL);
    p = p->next;
  }

  assert(__CPROVER_HEAP_path(x, NULL, "next"));
}



