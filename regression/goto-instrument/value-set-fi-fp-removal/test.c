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
  fp_t fp = f;
  fp();

  // this would fool an analysis that looks for functions whose address is taken
  fp_t other_fp = g;
}
