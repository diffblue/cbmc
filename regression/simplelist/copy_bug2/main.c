#include "../heap_builtins.h"

/* copy */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t x, y;
  list_t tmpx, tmpy, cell;
  list_t res, err;
 
  __CPROVER_assume(res!=err);

  if (x == NULL) {
    y = NULL;
    return;
  }

  y = (list_t)malloc(sizeof(struct list));
  not_null(y);
  y->next = NULL;
  not_null(x);
  y->value = x->value;
  not_null(x);
  tmpx = x->next;
  tmpy = y;

  while(tmpx != NULL) {
    cell = (list_t)malloc(sizeof(struct list));
    not_null(cell);
    not_null(tmpx);
    cell->value = tmpx->value;
    not_null(tmpy);
    tmpy->next = cell;
    cell->next = NULL; // BUG: line added
    tmpy = cell->next; //->next added (found with 2 unwindings)
    not_null(tmpx);
    tmpx = tmpx->next; 
  }

  not_null(tmpy);
  tmpy->next = NULL;

  assert(res!=err);
  assert(__CPROVER_HEAP_path(y, NULL, "next"));
}



