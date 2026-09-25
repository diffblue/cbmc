// N5008 [temp.variadic]/5: a pack expansion inside a braced-init-list
// produces one element per pack element; [class.static.data]/4 + [expr.const]:
// the initializer of a constexpr static data member is a constant expression,
// manifestly constant-evaluated.  Two defects in the static data member
// initializer of a class template: the pack expansion was NOT expanded (the
// list collapsed to its first element -- `count({sizeof(Ts)...})' was 1 for
// three types, a wrong value even at run time), and the initializer was not
// type-checked as a constant expression, so a constexpr function call in it
// never folded.  This is libc++ variant's
// `static constexpr _Trait __copy_constructible_trait =
//    __common_trait({__trait<_Types, ...>...});'.
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>

constexpr int count(std::initializer_list<int> xs)
{
  return xs.size();
}
constexpr int sum(std::initializer_list<int> xs)
{
  int s = 0;
  for(int x : xs)
    s += x;
  return s;
}
constexpr int twice(int x)
{
  return 2 * x;
}

struct X
{
  static constexpr int c = count({1, 2});
  static constexpr int t = twice(21);
};
template <class... Ts>
struct Y
{
  static constexpr int n = count({sizeof(Ts)...});
  static constexpr int s = sum({sizeof(Ts)...});
  static constexpr int m = count({1, sizeof(Ts)...});
  static constexpr int t = twice(sizeof...(Ts));
  static inline int rt = count({sizeof(Ts)...}); // not constexpr: run time
};

static_assert(X::c == 2 && X::t == 42, "non-template static members");
static_assert(Y<int, char, long>::n == 3, "count of a pack expansion");
static_assert(Y<int, char, long>::s == 13, "sum of a pack expansion");
static_assert(Y<int, char, long>::m == 4, "element before the expansion");
static_assert(Y<int, char, long>::t == 6, "sizeof...");
static_assert(Y<>::n == 0, "empty pack");

int main()
{
  __CPROVER_assert(Y<int, char, long>::rt == 3, "run-time static member");
  __CPROVER_assert(
    Y<int, char, long>::n + Y<int, char, long>::s == 16, "folded");
  __CPROVER_assert(Y<int, char, long>::rt == 1, "WRONG (must FAIL)");
}
