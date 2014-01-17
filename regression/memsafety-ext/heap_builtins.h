#include <stdlib.h>

extern __CPROVER_bool __CPROVER_HEAP_dangling(void* ptr);
extern __CPROVER_bool __CPROVER_HEAP_disjoint(void* ptr1, void* ptr2);
extern __CPROVER_bool __CPROVER_HEAP_path(void* ptr1, void* ptr2, void* f);
extern __CPROVER_bool __CPROVER_HEAP_onpath(void* ptr1, void* ptr2, void* ptr3, void* f);
