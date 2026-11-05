// std::common_reference_with<const W &, const W &> -- the same reference
// type on both sides -- holds; with libstdc++ 16's <concepts> and
// <type_traits> it takes another path through the common_reference
// machinery than with gcc 13's headers.  std::assignable_from,
// std::movable and std::copyable depend on it
// (cpp20_concept_conjunction_requires_params).
#include <concepts>
struct W
{
  int v = 0;
};
int main()
{
  static_assert(
    std::common_reference_with<const W &, const W &>, "same reference type");
  static_assert(std::assignable_from<W &, W>, "assignable_from");
  return 0;
}
