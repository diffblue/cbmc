#include <assert.h>

int main()
{
  int i = 1;
  int *p = &i;
  assert(*p == 1);
}
