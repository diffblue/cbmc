#include <assert.h>

const float plus_infinity = 1.0f/0.0f;
const float minus_infinity = 0.0f/-0.0f;
const float NaN = 0.0f * (1.0f/0.0f);

int main()
{
  _Bool temp;

  // NaN compared to anything should yield false
  temp = NaN < plus_infinity;
  assert(!temp);

  temp = NaN < minus_infinity;
  assert(!temp);

  temp = NaN <= NaN;
  assert(!temp);

  temp = NaN >= NaN;
  assert(!temp);

  temp = NaN > plus_infinity;
  assert(!temp);

  temp = NaN > minus_infinity;
  assert(!temp);

  temp = NaN > 0;
  assert(!temp);

  temp = NaN < 0;
  assert(!temp);

  return 0;
}
