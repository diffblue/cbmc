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
    assert(root != NULL);
    next = root->next;
    root = root->next; //BUG: found with 1 unwinding
    assert(root != NULL);
    root->next = new_root;
    new_root = root; 
    root = next;
  }

  assert(__CPROVER_HEAP_path(new_root, NULL, "next"));
  assert(res != err);
}



