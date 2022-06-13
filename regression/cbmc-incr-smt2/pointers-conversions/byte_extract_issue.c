#include <assert.h>
#include <stdint.h>

int main()
{
  uint32_t input;
  uint32_t original = input;
  uint8_t *ptr = (uint8_t *)(&input);
  assert(*ptr == 0); // falsifiable
  *ptr = ~(*ptr);
  assert(input != original); // valid
}
