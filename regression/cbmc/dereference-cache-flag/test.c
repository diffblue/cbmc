#include <assert.h>

int main(void)
{
  int cond, x, y, *p = cond ? &x : &y;
  assert(*p == 0);
}
