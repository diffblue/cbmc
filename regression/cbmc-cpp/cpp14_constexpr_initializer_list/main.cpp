// N5008 [dcl.init.list]/5-6 and [expr.const]: a std::initializer_list<E>
// argument is a pair (pointer to the first element of a backing array of E
// with static storage duration, length); the elements are constant
// expressions, so a constexpr function may read them through begin()/end(),
// size(), and a range-for.  The constant evaluator tracked a pointer into a
// string literal only; now a pointer into ANY array of constants (the
// backing array is a static object with an array constant value,
// [expr.const]/11), pointer arithmetic and comparison, `this' for a member
// call on a tracked object (`xs.size()'), and a reference bound to a tracked
// variable (`auto &&__range = xs' of the range-for lowering).  libc++'s
// variant computes its traits with `__common_trait({...})' this way.
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>

constexpr int count(std::initializer_list<int> xs)
{
  return xs.size();
}
constexpr int first(std::initializer_list<int> xs)
{
  return *xs.begin();
}
constexpr int last(std::initializer_list<int> xs)
{
  return *(xs.end() - 1);
}
constexpr int sum(std::initializer_list<int> xs)
{
  int s = 0;
  for(int x : xs)
    s += x;
  return s;
}
constexpr int sum_it(std::initializer_list<int> xs)
{
  int s = 0;
  for(const int *p = xs.begin(); p != xs.end(); ++p)
    s += *p;
  return s;
}
enum class Trait
{
  Trivial,
  Available,
  Unavailable
};
constexpr Trait common(std::initializer_list<Trait> ts)
{
  Trait r = Trait::Trivial;
  for(Trait t : ts)
    if(static_cast<int>(t) > static_cast<int>(r))
      r = t;
  return r;
}

static_assert(count({1, 2, 3}) == 3, "size");
static_assert(count({}) == 0, "empty");
static_assert(first({7, 8}) == 7, "begin");
static_assert(last({7, 8, 9}) == 9, "end - 1");
static_assert(sum({1, 2, 3}) == 6, "range-for");
static_assert(sum_it({4, 5, 6}) == 15, "iterator loop");
static_assert(
  common({Trait::Trivial, Trait::Available}) == Trait::Available,
  "common");
static_assert(common({Trait::Trivial}) == Trait::Trivial, "common single");

int main()
{
  constexpr int s = sum({10, 20, 30});
  static_assert(s == 60, "block scope");
  int r = s;
  __CPROVER_assert(r == 60, "folded value at run time");
  __CPROVER_assert(r == 61, "WRONG (must FAIL)");
}
