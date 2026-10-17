// N5008 [concept.commonref], [meta.trans.other]/5: common_reference_t<W &,
// const W &> is `const W &' (COMMON-REF of two lvalue references: an lvalue
// reference to the cv-union of the referenced types), so
// common_reference_with<W &, const W &> holds.  The front end evaluates the
// concept false: libstdc++'s __common_ref chain (`decltype(false ? declval<
// __copy_cv<_Xp, _Yp> &>() : declval<__copy_cv<_Yp, _Xp> &>())') is not
// reduced.  Note the same_as / const-const cases hold.
#include <concepts>
struct W
{
  int v = 0;
};
int main()
{
  static_assert(std::common_reference_with<const W &, const W &>, "same type");
  static_assert(
    std::common_reference_with<W &, const W &>,
    "cv-differing lvalue references");
  static_assert(
    std::same_as<std::common_reference_t<W &, const W &>, const W &>,
    "common_reference_t is const W &");
  return 0;
}
