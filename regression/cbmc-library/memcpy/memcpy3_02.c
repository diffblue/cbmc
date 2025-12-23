#include <assert.h>
#include <string.h>

int main()
{
  int A[3] = {1, 2, 3};
  int *p = A;
  int v1, v2;

  memcpy(&v1, p, sizeof(int));
  ++p;
  memcpy(&v2, p, sizeof(int));

  assert(v1 == 1);
  assert(v2 == 2);

  return 0;
}
