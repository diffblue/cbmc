#include "../heap_builtins.h"

/* insert */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, y;
  // value to be inserted
  list_t val;

  x = (list_t)malloc(sizeof(struct list));
  assert(x != NULL);
  x->value = val;
  assert(x != NULL);
  x->next = y;

  assert(__CPROVER_HEAP_path(x, y, "next"));
}



