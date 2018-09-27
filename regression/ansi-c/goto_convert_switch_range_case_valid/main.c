#include <assert.h>

#define false 0

int main(void)
{
  int x = 5;
  switch (x)
  {
    case 0 ... 10:
      break;
    default:
      assert(false);
      break;
  }
}
