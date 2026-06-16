// A class-template partial specialization keyed on the reference qualifier of
// its argument: `S<T&>` vs `S<T&&>` (N5008 [temp.spec.partial.match],
// [temp.deduct.type]).  The lvalue-reference specialization must be selected
// for an lvalue-reference argument and the rvalue-reference specialization for
// an rvalue-reference argument; the `&` / `&&` qualifier is part of the
// pattern and distinguishes the two.
//
// Previously CBMC's template-argument deduction stripped a reference pattern
// to its referent without checking the reference *kind* (in CBMC an rvalue
// reference is a pointer carrying both the reference and rvalue-reference
// flags), so `S<T&>` and `S<T&&>` both matched any reference argument.  The
// wrong specialization was then selected -- e.g. `S<int&&>` resolved to the
// `S<T&>` specialization.  This is the mechanism behind libstdc++'s
// reference-qualifier-keyed `std::__common_ref_impl<_Xp&, _Yp&&>` family
// (used by C++20 `common_reference`): mis-selecting
// `__common_ref_impl<_Xp&, _Yp&&> : __common_ref_impl<_Yp&&, _Xp&>` makes the
// substituted base equal the specialization itself (a self-inheriting class,
// forbidden by [class.derived.general]/2), which aborts class-body
// elaboration.  See doc/architectural/cpp-requires-expression-support.md.

template <typename>
struct S;

template <typename T>
struct S<T &>
{
  static constexpr int v = 1;
};

template <typename T>
struct S<T &&>
{
  static constexpr int v = 2;
};

int main()
{
  __CPROVER_assert(S<int &>::v == 1, "lvalue-reference specialization selected");
  __CPROVER_assert(
    S<int &&>::v == 2, "rvalue-reference specialization selected");
  return 0;
}
