#include <assert.h>
#include <stdint.h>

union my_uniont
{
  uint16_t a;
  uint8_t b;
};

int main()
{
  union my_uniont my_union = {.b = 5};
  assert(my_union.a == 5);
}
