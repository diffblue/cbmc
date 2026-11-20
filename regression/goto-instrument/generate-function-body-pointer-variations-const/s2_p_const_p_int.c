#include <assert.h>

// Multi-level pointer const variation: int * const * (pointer to a const
// pointer to int). The immediate pointee type `int * const` is const, so the
// havoc generator skips the whole parameter (empty body): nothing changes.
//
// Characterization note (#1948): this pins current, over-restrictive
// behaviour. A real callee could legally write **pp (the underlying int is not
// const); the generator nevertheless does nothing. Update the expectation if
// the generator learns to havoc non-const data behind a const pointer.
void havoc_p_const_p_int(int *const *pp);

int main(void)
{
  int b = 2;
  int *pb = &b;
  int *const *pp = &pb;

  assert(b == 2);    // baseline
  assert(**pp == 2); // baseline

  havoc_p_const_p_int(pp);

  assert(b == 2);    // empty body: SUCCESS
  assert(**pp == 2); // empty body: SUCCESS

  return 0;
}
