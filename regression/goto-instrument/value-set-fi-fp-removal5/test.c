#include <assert.h>

typedef void (*fp_t)();

void f(int x)
{
}

void g(int y)
{
}

int main(void)
{
  // the value set is empty, defaults to standard function pointer removal behaviour
  fp_t other_fp = g;

  fp_t fp;
  fp();
}
