// KNOWNBUG (N5008 [temp.spec.partial.match]/2, [temp.deduct]/8, [expr.cond]/4).
//
// A class-template partial specialization is selected when the SFINAE check in
// its argument list -- here `void_t<decltype(false ? declval<A>() :
// declval<B>())>` -- is well-formed, and is rejected (falling back to the
// primary template) when that conditional-expression has no common type and is
// therefore ill-formed.  Substitution failure in the immediate context is not
// an error ([temp.deduct]/8); it just removes the specialization from
// consideration.
//
// This is the minimal, self-contained essence of libstdc++'s C++20
// `std::__common_ref_impl<_Xp&, _Yp&, void_t<__condres_cvref<_Xp, _Yp>>>`
// family (used by `common_reference`, reached via the iterator concepts when a
// `reverse_iterator` member of `std::basic_string` / `std::vector` is
// instantiated).
//
// DIVERGENCE: when the partial specialization is selected for a **member of a
// class template** (instantiated as part of the enclosing class's body), CBMC
// fails to treat the ill-formed conditional `decltype` as a substitution
// failure, so it wrongly selects the specialization for `cref<int, int*>`
// (which has no common type).  The very same construct used as a function-body
// local works (see cpp20_partial_spec_conditional_sfinae), so this is a
// context-dependent partial-spec/SFINAE evaluation bug, not a parsing bug.
//
// When fixed, reclassify this test to CORE.

template <class X>
X declval();

template <class...>
using void_t = void;

template <class A, class B>
using cond_res = decltype(false ? declval<A>() : declval<B>());

template <class A, class B, class = void>
struct cref
{
  int tag = 1; // primary
};

template <class A, class B>
struct cref<A, B, void_t<cond_res<A, B>>>
{
  int tag = 2; // selected iff A and B have a common type
};

template <class T>
struct Outer
{
  cref<T, T> same;    // T, T -> common type exists -> specialization (tag 2)
  cref<int, T *> diff; // int, int* -> no common type -> primary (tag 1)
  int v;
  Outer() : v(7) {}
};

int main()
{
  Outer<int> o;
  __CPROVER_assert(o.v == 7, "class body fully elaborated");
  __CPROVER_assert(o.same.tag == 2, "common type -> specialization");
  __CPROVER_assert(o.diff.tag == 1, "no common type -> primary");
  return 0;
}
