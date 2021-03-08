#include <assert.h>
#include <string.h>

int main(void)
{
  int src[8], dst[8], delta;
  if(delta == 3 || delta == 4)
  {
    memcpy(dst, src, sizeof(int) * delta);
    assert(dst[1] == src[1]);
  }
  return 0;
}
