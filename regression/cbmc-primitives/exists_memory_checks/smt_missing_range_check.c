#include <assert.h>
#include <stdlib.h>

int main()
{
  int *a = calloc(10, sizeof(int));
  a[5] = 25;

  assert(__CPROVER_exists {
    int i;
    a[i] == i *i
  });
}
