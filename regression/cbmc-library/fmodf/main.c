#include <assert.h>
#include <math.h>

int main()
{
  // examples from
  // https://stackoverflow.com/questions/2947044/how-do-i-use-modulus-for-float-double
  // and
  // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
  float d1 = fmodf(0.5f, 0.3f);
  assert(d1 > 0.19f && d1 < 0.21f);
  float d2 = fmodf(-0.5f, 0.3f);
  assert(d2 > -0.21f && d2 < -0.19f);
  float x = 7.5f, y = 2.1f;
  float xModY = fmodf(x, y);
  assert(xModY > 1.19f && xModY < 1.21f);
}
