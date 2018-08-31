#include <assert.h>

int main()
{
  int i = 0;
  int *p = &i;
  assert(*p == 0);
  return 0;
}
