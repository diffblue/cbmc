#include <stdint.h>
#include <string.h>

int main()
{
  uint8_t a;
  uint32_t b;

  memcpy(&b, &a, sizeof(b));

  return 0;
}
