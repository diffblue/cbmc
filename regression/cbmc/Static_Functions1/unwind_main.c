#include <assert.h>

// unwind_a.c and unwind_b.c both define a file-local (static) function named
// count, each containing a loop. After linking, the second definition is
// renamed, so the two loops carry distinct identifiers: count.0 (unwind_a.c)
// and count$link1.0 (unwind_b.c). This shows those identifiers can be used
// with --unwindset to bound each loop independently.
int a_entry(int n);
int b_entry(int n);

int main(void)
{
  assert(a_entry(3) == 3);
  assert(b_entry(3) == 6);
}
