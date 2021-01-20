#include <assert.h>

int main()
{
  char *c14 = "\x0E";
  assert(c14[0] == 14);
  assert(c14[1] == 0);
  assert(c14[0] != 14);
}
