#include <assert.h>

int main()
{
  int k1 = 5 / 2;
  assert(k1 == 2);
  
  int k2 = -5 / 2;
  assert(k2 == -2);

  int k3 = 5 / -2;
  assert(k3 == -2);

  int k4 = -5 / -2;
  assert(k4 == 2);
}
