#include <stdio.h>
#include <assert.h>

int main()
{
  printf("PRINT d1 %d, %d\n", 123, -123);
  printf("PRINT g1 %g, %g, %g, %g\n", 123.0, -123.0, 123.123, 0.123);
  printf("PRINT e1 %e, %e, %e, %e\n", 123.0, -123.0, 123.123, 0.123);
  printf("PRINT f1 %f, %f, %f, %f\n", 123.0, -123.0, 123.123, 0.123);
  assert(0);
}
