#include <assert.h>
#include <stddef.h>

// Must match --object-bits in test.desc.
#define OBJECT_BITS 16

int main()
{
  char x, y;
  char *p = &x;
  char *p2 = &y;
  size_t k;

  char *w1 = p + k;
  char *w2 = p2 + k;

  // The smallest offset that does not fit the offset field of the pointer
  // encoding.
  const size_t wrap = (size_t)1 << (sizeof(char *) * 8 - OBJECT_BITS);

  if(k == wrap)
  {
    // Pointer arithmetic whose result offset does not fit the offset field
    // yields a pointer to an unknown (nondeterministic) address: neither
    // equality nor inequality between two such pointers is provable. In
    // particular, equality must NOT be provable (identically-shifted
    // pointers into disjoint objects are never equal under any concrete
    // address assignment).
    assert(w1 == w2);
    assert(w1 != w2);
  }

  return 0;
}
