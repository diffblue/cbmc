#include <assert.h>

int main()
{
#if 0
  // examples of constants that previously exhibited wrong behaviour
  union U
  {
    double d;
    uint64_t b;
  };
  union U u = {
    .b = 0b0000000000000011111111111111111111111110000001000000000000000000};
  union U u2 = {
    .b = 0b0000000000000000000000000000001111111111111111111111111000000000};
  double d = u.d;
#else
  double d;
#endif
  float f;
  if(d > 0.0 && d < 1.0)
  {
    f = d;
    assert(f <= 1.0f);
  }
  return 0;
}
