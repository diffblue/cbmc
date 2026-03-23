#include <assert.h>
#include <math.h>

int main()
{
  // example from
  // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
  double x = 7.5, y = 2.1;
  double xModY = remainder(x, y);
  assert(xModY > -0.91 && xModY < -0.89);
}
