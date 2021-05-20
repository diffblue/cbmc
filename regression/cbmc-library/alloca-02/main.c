#include <stdlib.h>

#ifdef _WIN32
void *alloca(size_t alloca_size);
#endif

int *foo()
{
  int *foo_ptr = alloca(sizeof(int));
  return foo_ptr;
}

int main()
{
  int *from_foo = foo();
  *from_foo = 42; // access to object that has gone out of scope

  return 0;
}
