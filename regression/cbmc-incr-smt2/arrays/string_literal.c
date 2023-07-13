#include <assert.h>
#include <stdint.h>

int main()
{
  const char *my_string = "hello!";
  uint8_t index;
  __CPROVER_assume(index < 6);
  char element = my_string[index];
  assert(element != 'o');
}
