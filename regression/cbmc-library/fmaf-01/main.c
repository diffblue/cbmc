#include <assert.h>
#include <math.h>

int main()
{
  float five = fmaf(1.0f, 2.0f, 3.0f);
  assert(five > 4.99f && five < 5.01f);
  return 0;
}
