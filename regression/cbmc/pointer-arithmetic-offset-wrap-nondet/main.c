#include <assert.h>
#include <stdint.h>

int main()
{
  char x, y;
  char *p = &x;
  char *p2 = &y;
  uint64_t k;

  char *w1 = p + k;
  char *w2 = p2 + k;

  if(k == (1ULL << 48))
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
