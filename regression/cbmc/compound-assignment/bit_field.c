#include <assert.h>

struct S
{
  unsigned int value : 3;
};

int main(void)
{
  struct S s = {2};
  s.value *= 1.5f;
  assert(s.value == 3);

  s.value = 2;
  unsigned int result = s.value *= 1.5f;
  assert(s.value == 3);
  assert(result == 3);
}
