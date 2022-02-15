#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int main()
{
  size_t len;
  __CPROVER_assume(0 < len);
  uint16_t *data = malloc(len * sizeof(uint16_t));
  if(data)
  {
    len = (len + 1) * sizeof(uint16_t);
    uint16_t *ptr = malloc(len);
    if(ptr)
    {
      memcpy(ptr, data, len);
      ptr[len] = 0;
    }
  }
  return 0;
}
