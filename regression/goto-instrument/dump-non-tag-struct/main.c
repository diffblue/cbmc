#include <stdlib.h>

int main()
{
  // CBMC's model of calloc includes an overflow check, which in turn creates a
  // struct that holds both the arithmetic result and the overflow information.
  // dump-c did not support this struct defined in place.
  calloc(10, 1);
}
