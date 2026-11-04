#include <assert.h>
#include <math.h>

int main()
{
  // example from
  // https://stackoverflow.com/questions/25734144/difference-between-c-functions-remainder-and-fmod
  float x = 7.5f, y = 2.1f;
  float xModY = remainderf(x, y);
  assert(xModY > -0.91f && xModY < -0.89f);
}
