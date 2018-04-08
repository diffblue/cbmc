#include <assert.h>

int main()
{
  int i, j;

  // counter must be reset for inner loop
  // or the assertion is missed
  for(j=0; j<2; j++)
    for(i=0; i<100; i++);

  assert(0);
}
