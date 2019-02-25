#include <stdlib.h>

#define BUG

int* x;
_Bool set_done;

void* set_x(void* arg) {
  *x = 10;
  assert(/*x!=NULL && */*x==10);
  set_done=1;
}

int main() {
  x = malloc(sizeof(int));
  #ifdef BUG
  __CPROVER_ASYNC_1: set_x(NULL);
  __CPROVER_assume(set_done);
  #else
  set_x(NULL);
  #endif
  assert(/*x!=NULL && */*x==10);
  return 0;
}
