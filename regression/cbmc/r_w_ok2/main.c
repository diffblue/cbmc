#include <assert.h>

int main()
{
  int *p = (int *)0;

  _Bool not_ok = !__CPROVER_r_ok(p, sizeof(int));
  assert(not_ok);

  if(__CPROVER_w_ok(p, sizeof(int)))
    assert(0);
}
