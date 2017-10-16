#include <assert.h>

void main()
{
  unsigned char n;
  __CPROVER_assume(n > 0);   // To keep division well defined
  __CPROVER_assume(n * n > 0);   // To keep division well defined

  unsigned char i = 0;
  unsigned char j = 0;

  unsigned char aux1 = i / (n * n);
  for (i = 0; i < n; ++i, aux1 = i / (n * n)) {
    for (j = 0; j < n; ++j) {
    }
  }
  assert(i != n);
}
