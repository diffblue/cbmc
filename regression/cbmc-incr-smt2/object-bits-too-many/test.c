#include <assert.h>
#include <stdlib.h>

// Regression test for the object-bits bound check in the incremental SMT2
// backend (convert_expr_to_smt). Allocating more objects than 2^object_bits
// must raise a graceful "too many addressed objects" diagnostic rather than an
// invalid shift of std::size_t(1) by object_bits.
int main()
{
  for(int i = 0; i < 20; ++i)
  {
    char *p = malloc(1);
    assert(p != 0);
  }
  return 0;
}
