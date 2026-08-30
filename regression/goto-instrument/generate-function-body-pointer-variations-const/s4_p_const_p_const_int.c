#include <assert.h>

// Multi-level pointer const variation: const int * const * (pointer to a const
// pointer to const int). The immediate pointee `const int * const` is const,
// so the havoc generator skips the parameter (empty body): nothing changes.
void havoc_p_const_p_const_int(const int *const *pp);

int main(void)
{
  int d = 4;
  const int *cpd = &d;
  const int *const *pp = &cpd;

  assert(d == 4);    // baseline
  assert(**pp == 4); // baseline

  havoc_p_const_p_const_int(pp);

  assert(d == 4);    // empty body: SUCCESS
  assert(**pp == 4); // empty body: SUCCESS

  return 0;
}
