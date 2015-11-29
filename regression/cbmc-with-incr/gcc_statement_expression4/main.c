#include <assert.h>

void foo(const void* p)
{
  assert(*((char*)p)==42);
}

int main()
{
  char st[1];

  foo(({
      st[0]=42;
      st;
      }));

  foo(({
      const char* p;
      p=st;
      }));

  foo(({
      (const void*)st;
      }));

  return 0;
}
