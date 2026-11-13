#include <assert.h>
#include <math.h>

int main()
{
  // example from
  // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
  long double x = 7.5l, y = 2.1l;
  long double xModY = remainderl(x, y);
  assert(xModY > -0.91l && xModY < -0.89l);
}
