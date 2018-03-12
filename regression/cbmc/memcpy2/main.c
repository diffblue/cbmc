#include <assert.h>
#include <string.h>

int main()
{
  char A[3] = {'a', 'b', 'c'};
  char *p = A;
  char v1, v2;

  memcpy(&v1, p, 1);
  ++p;
  memcpy(&v2, p, 1);

  assert(v1 == 'a');
  assert(v2 == 'b');

  return 0;
}
