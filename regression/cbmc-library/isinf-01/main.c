#include <assert.h>
#include <math.h>

#ifdef __GNUC__

void f00(float f)
{
  if(f > 0x1.FFFFFEp+127)
  {
    assert(isinf(f));
  }
}

#endif

int main(void)
{
#ifdef __GNUC__
  float f;

  f00(f);
#endif

  return 0;
}
