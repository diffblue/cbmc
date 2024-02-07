#include <assert.h>
#include <math.h>

int main()
{
  long double five = fmal(1.0l, 2.0l, 3.0l);
  assert(five > 4.99l && five < 5.01l);
  return 0;
}
