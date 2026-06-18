// A constrained constructor template whose requires-clause is *not* satisfied
// must be removed from overload resolution ([temp.constr.decl]/1,
// [over.match.viable]) so a better-constrained / unconstrained constructor is
// chosen instead.
//
// This mirrors libstdc++ std::span's two constructors:
//   span(pointer __first, size_type __count);                       // (1)
//   template<contiguous_iterator _It, sized_sentinel_for<_It> _End>
//     requires (!is_convertible_v<_End, size_type>)
//   span(_It __first, _End __last);                                 // (2)
// For `span(ptr, 5)` the second argument 5 (int) is convertible to size_type,
// so constructor (2)'s requires-clause `!is_convertible_v<_End, size_type>` is
// *false* and (2) must be discarded, leaving (1).  CBMC used to leave the
// substituted atomic constraint `is_convertible_v<int, unsigned long>` as an
// unfolded comparison (notequal(1, 0)); the tri-state constraint evaluator then
// reported "unknown" and kept (2), which was wrongly selected.
//
// Here `which == 1` holds iff the unconstrained (pointer, count) constructor is
// selected.  The assertion is non-vacuous: were the constrained overload kept,
// `which` would be 2.
#include <type_traits>

struct S
{
  int which;
  S(int *, unsigned long) : which(1) {}
  template <typename U>
  requires(!std::is_convertible_v<U, unsigned long>)
  S(int *, U) : which(2)
  {
  }
};

int main()
{
  int arr[3];
  S s(arr, 2); // 2 (int) is convertible to unsigned long -> overload (2) removed
  __CPROVER_assert(
    s.which == 1, "unsatisfied requires-clause removes the constrained ctor");
  return 0;
}
