#include <assert.h>
#include <stdlib.h>

int main()
{
  int A[1];

  assert(__CPROVER_r_ok(A, sizeof(int)));
}
