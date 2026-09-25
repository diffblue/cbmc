// Test for issue #8161: consistent pointer comparison
// Both assertions should fail (or both succeed)
#include <assert.h>
extern int nondet_int();
int main()
{
  int m = nondet_int();
  int *n = &m;

  if((unsigned long)n >= (unsigned long)(-4095))
    assert((unsigned int)(-1 * (long)n) < 6);

  int a = -2048;
  if((unsigned long)a >= (unsigned long)(-4095))
    assert((unsigned int)(-1 * (long)a) < 6);
}
