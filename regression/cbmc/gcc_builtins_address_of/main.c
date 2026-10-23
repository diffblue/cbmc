#include <assert.h>

int main()
{
  void (*f)(int) = __builtin_exit;
  int (*g)(float) = __builtin_isnanf;
  assert(!g(3.14f));
  f(1);
  assert(0);
  return 0;
}
