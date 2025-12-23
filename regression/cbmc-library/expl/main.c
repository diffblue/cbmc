#include <assert.h>
#include <math.h>

int main()
{
  long double e = expl(1.0l);
  assert(e > 2.713l && e < 2.886l);
  return 0;
}
