#include <assert.h>
#include <math.h>

int main()
{
  double five = fma(1.0, 2.0, 3.0);
  assert(five > 4.99 && five < 5.01);
  return 0;
}
