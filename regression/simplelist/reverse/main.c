#include "../heap_builtins.h"

/* reverse */

/* expect bottom */

struct list {
  struct list* value;
  struct list* next;
};

typedef struct list* list_t;

void main() {
  list_t root, new_root, res, err;
  list_t next;

  __CPROVER_assume(res!=err);
  new_root = NULL;

  while (root != NULL) {
    not_null(root);
    next = root->next;
    not_null(root);
    root->next = new_root;
    new_root = root;
    root = next;
  }

  assert(__CPROVER_HEAP_path(new_root, NULL, "next"));
  assert(res != err);
}



