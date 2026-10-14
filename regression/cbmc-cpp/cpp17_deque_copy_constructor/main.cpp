// N5008 [sequence.reqmts], [deque.cons]: copying a std::deque copies its
// elements.  The front end's model of std::__uninitialized_copy_a copies
// between pointers with __CPROVER_array_replace; for deque's
// _Deque_iterator arguments it was applied to the iterator objects and
// symbolic execution failed an invariant ("pointer.type().id() ==
// ID_pointer"; `std::deque<bool>' copies in CBMC's own goto-symex state,
// dog-fooding).  Non-pointer iterators keep the library's own body.
extern "C" void __CPROVER_assert(bool, const char *);
#include <deque>
int main()
{
  std::deque<bool> d{true, false};
  std::deque<bool> e(d);
  __CPROVER_assert(e.size() == 2, "copied size");
  __CPROVER_assert(e[0] && !e[1], "copied elements");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
