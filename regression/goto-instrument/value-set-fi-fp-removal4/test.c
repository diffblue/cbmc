#include <assert.h>

typedef void (*fp_t)();

void f()
{
}

void g()
{
}

int main(void)
{
  // the value set for fp is empty, defaults to standard function pointer removal behaviour
  fp_t other_fp = g;
  other_fp = f;

  fp_t fp;
  fp();
}
