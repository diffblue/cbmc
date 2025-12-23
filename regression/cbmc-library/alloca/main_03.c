#include <stdlib.h>

#ifdef _WIN32
void *alloca(size_t alloca_size);
#endif

typedef int *int_ptr;

int_ptr global;

void foo()
{
  int_ptr ptr[2];
  for(int i = 0; i < 2; ++i)
  {
    ptr[i] = alloca(sizeof(int));
  }
  *(ptr[0]) = 42;
  *(ptr[1]) = 42;

  _Bool nondet;
  if(nondet)
    global = ptr[0];
  else
    global = ptr[1];
}

int main()
{
  foo();
  *global = 42;
}
