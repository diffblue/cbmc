#include <assert.h>

struct test
{
  unsigned int a;
  unsigned int b;
};

int main()
{
  struct test t;
  if(t.a > 10)
    assert(t.a > 0);
}
