// N5008 [temp.deduct.call]/3: in class template argument deduction an rvalue
// reference to a template parameter OF THE CLASS TEMPLATE is not a forwarding
// reference; [dcl.init.general]/9: value-initialising a reference is
// ill-formed (a requirement naming it is unsatisfied, not a crash).
extern "C" void __CPROVER_assert(bool, const char *);
#include <concepts>
#include <utility>

template <typename R>
requires std::movable<R> struct owning
{
  R r = R();
  constexpr owning(R &&x) : r(std::move(x))
  {
  }
};

template <typename R>
concept can_own = requires
{
  owning{std::declval<R>()};
};

struct box
{
  int v;
};

template <typename T>
struct wrap
{
  T t;
  wrap(T &&x) : t(std::move(x))
  {
  }
};

int main()
{
  // an array lvalue: R deduced as int[5] (not int(&)[5]); int[5] is not
  // movable, so the constraint fails and the requirement is false
  static_assert(!can_own<int(&)[5]>, "array lvalue cannot be owned");
  static_assert(can_own<box>, "a movable class can be owned");
  box b{4};
  owning o{std::move(b)};
  static_assert(__is_same(decltype(o), owning<box>), "deduced box");
  __CPROVER_assert(o.r.v == 4, "moved value");
  int i = 9;
  wrap w{std::move(i)};
  static_assert(__is_same(decltype(w), wrap<int>), "T = int, not int&&");
  __CPROVER_assert(w.t == 9, "wrapped value");
  __CPROVER_assert(o.r.v == 5, "WRONG (must FAIL)");
  return 0;
}
