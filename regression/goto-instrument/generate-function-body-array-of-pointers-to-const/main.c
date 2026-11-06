#include <assert.h>

// Edge case: array of pointers where each pointer points to const data.
// The parameter const int **arr has immediate pointee type `const int *` (a
// non-const pointer), so the havoc generator reinitialises *arr, i.e. arr[0]
// only. The remaining elements arr[1], arr[2] are left untouched.

void havoc_array_of_pointers_to_const(const int **arr, int size);

int main(void)
{
  int a = 10, b = 20, c = 30;
  const int *arr[] = {&a, &b, &c};

  assert(a == 10);       // 1
  assert(b == 20);       // 2
  assert(c == 30);       // 3
  assert(*arr[0] == 10); // 4
  assert(*arr[1] == 20); // 5
  assert(*arr[2] == 30); // 6

  havoc_array_of_pointers_to_const(arr, 3);

  // The named locals a, b, c are never reached by the havoc, so they are
  // preserved.
  assert(a == 10); // 7: SUCCESS
  assert(b == 20); // 8: SUCCESS
  assert(c == 30); // 9: SUCCESS

  // arr[0] (== *arr) was redirected to a fresh nondet object, so reading
  // through it may observe a different value.
  assert(*arr[0] == 10); // 10: FAILURE

  // arr[1] and arr[2] are NOT havoc'd, so semantically these ought to remain
  // provable SUCCESS. CBMC currently reports them as UNKNOWN: dereferencing the
  // redirected (and nondet-nullable) arr[0] above introduces undecidable
  // pointer-safety properties that leave the following dereferences undecided.
  // That UNKNOWN is an incompleteness, not a guarantee, and shifts with
  // solver/CBMC changes, so we deliberately do not pin assertions 11 and 12.
  assert(*arr[1] == 20); // 11: UNKNOWN (not asserted; see above)
  assert(*arr[2] == 30); // 12: UNKNOWN (not asserted; see above)

  return 0;
}
