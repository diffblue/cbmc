#include <assert.h>
#include <stdbool.h>

int main()
{
  float zero = 0.0f;
  float one = 1.0f;
  double dzero = 0.0;
  float complex = 0x1p+37f;

  assert(false);

  return 0;
}

void test(float value)
{
  assert(value == 1.0f);
  assert(value == 0.0f);
}
