#include <assert.h>

int main()
{
  int v, x, x_before;
  x_before = x;

  __atomic_store_n(&x, 42, 0);
  __atomic_store(&x, &x_before, 0);

  assert(__atomic_load_n(&x, 0) == x_before);
  __atomic_load(&x_before, &x, 0);
  assert(x == x_before);

  assert(__atomic_exchange_n(&x, 42, 0) == x_before);
  __atomic_exchange(&x, &v, &x_before, 0);

  assert(__atomic_compare_exchange_n(&x, &v, 42, 0, 0, 0));
  v = 42;
  assert(__atomic_compare_exchange(&x, &v, &v, 0, 0, 0));

  return 0;
}
