#include <assert.h>

typedef void (*fp_t)();

void f()
{
}

int main(void)
{
  fp_t fp = f;
  goto L;

L:
  fp();
}
