// std::common_reference_with<const W &, const W &> -- the same reference
// type on both sides -- is false with libstdc++ 16's <concepts>/<type_traits>
// (the common_reference machinery there takes a path the front end
// mis-evaluates), so every std::assignable_from / std::movable /
// std::copyable check, and cpp20_concept_conjunction_requires_params, fails
// ("static assertion failed").  With gcc 13's headers it holds.
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
