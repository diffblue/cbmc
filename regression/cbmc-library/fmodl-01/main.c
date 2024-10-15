#include <assert.h>
#include <math.h>

int main()
{
  // examples from
  // https://stackoverflow.com/questions/2947044/how-do-i-use-modulus-for-float-double
  // and
  // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
  long double d1 = fmodl(0.5l, 0.3l);
  assert(d1 == 0.2l);
  long double d2 = fmodl(-0.5l, 0.3l);
  assert(d2 == -0.2l);
  long double x = 7.5l, y = 2.1l;
  long double xModY = fmodl(x, y);
  assert(xModY > 1.19l && xModY < 1.21l);
}
