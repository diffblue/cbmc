// A library function body the front-end cannot type-check is dropped and the
// function becomes a havoc stub: every call returns nondet.  That used to
// happen silently; the drop is now reported.
extern "C" void __CPROVER_assert(bool, const char *);
#include "../cpp11_dropped_library_body_warning/include/lib.hpp"
int main()
{
  __CPROVER_assert(good_fn(1) == 2, "good");
  int r = bad_fn(1);
  __CPROVER_assert(r == r, "bad_fn is a havoc stub (no-body property fails)");
  return 0;
}
