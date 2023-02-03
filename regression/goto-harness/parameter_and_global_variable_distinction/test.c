#include <assert.h>

typedef int (*fptr_t)(void);

fptr_t f;

int call_f()
{
  assert(f == ((void *)0));
  return 0;
}

void function(fptr_t f)
{
  if(f != ((void *)0))
    assert(f() == call_f());
  assert(f != ((void *)0));
}
