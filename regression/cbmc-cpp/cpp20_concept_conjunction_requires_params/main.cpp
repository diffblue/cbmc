// C++20: a requires-expression that is only a *conjunct* of a larger
// constraint-expression (not the whole concept body) must still have its
// requirement-parameter-list bound ([expr.prim.req.general]/2).  This is the
// shape of std::assignable_from / std::movable / std::copyable, which combine a
// concept-id conjunct with a parametered requires-expression.  Exercises the
// real library concepts over a regular copyable/movable class.

#include <concepts>

struct W
{
  int v = 0;
  W() = default;
  W(const W &) = default;
  W(W &&) = default;
  W &operator=(const W &) = default;
  W &operator=(W &&) = default;
  ~W() = default;
};

// A hand-written mirror of the assignable_from shape: a concept-id conjunct
// followed by a parametered requires-expression.
template <class _Lhs, class _Rhs>
concept my_assignable_from =
  std::common_reference_with<const std::remove_reference_t<_Lhs> &,
                             const std::remove_reference_t<_Rhs> &> &&
  requires(_Lhs __lhs, _Rhs &&__rhs) {
    { __lhs = static_cast<_Rhs &&>(__rhs) } -> std::same_as<_Lhs>;
  };

int main()
{
  // Hand-written conjunction-with-parametered-requires.
  static_assert(my_assignable_from<W &, W>, "W& = W&& yields W&");

  // Real library concepts of the same shape.
  static_assert(std::assignable_from<W &, W>, "assignable_from");
  static_assert(std::movable<W>, "movable");
  static_assert(std::copyable<W>, "copyable");

  // Negative: int is not assignable through a const-ref lhs.
  static_assert(!std::assignable_from<const int &, int>, "const lhs");

  return 0;
}
