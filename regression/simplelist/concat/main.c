#include "../heap_builtins.h"

/* concat */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, y,tmp;

  tmp = x;

  if(x == NULL) {
    x = y;
    return;
  }

  not_null(tmp);
  while(tmp->next != NULL) {
    not_null(tmp);
    tmp = tmp->next;
  }

  not_null(tmp);
  tmp->next = y;

  assert(__CPROVER_HEAP_path(x, tmp, "next"));
}



