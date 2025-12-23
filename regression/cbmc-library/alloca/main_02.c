#include <stdlib.h>

#ifdef _WIN32
void *alloca(size_t alloca_size);
#endif

// intentionally type conflicting: the built-in library uses const void*; this
// is to check that object type updates are performed
extern const char *__CPROVER_alloca_object;

int *foo()
{
  int *foo_ptr = alloca(sizeof(int));
  __CPROVER_assert(foo_ptr == __CPROVER_alloca_object, "may fail");
  return foo_ptr;
}

int main()
{
  int *from_foo = foo();
  *from_foo = 42; // access to object that has gone out of scope

  return 0;
}
