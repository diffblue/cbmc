#include <cassert>

int main()
{
  int i;

  // this is to parse as (bool(i)) & 0x1fff
  // and not as bool(i&0x1fff)
  
  assert(sizeof((bool)(i) & 0x1fff)==sizeof(int));

  return 0;
}
