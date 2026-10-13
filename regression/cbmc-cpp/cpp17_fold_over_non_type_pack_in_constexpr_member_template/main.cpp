// N5008 [expr.prim.fold]/2-3, [temp.variadic]/7: `(100 + ... + Is)' is
// 100 + 1 + 2 for Is = {1, 2} and 100 for an empty Is.  A constexpr member
// function template is converted eagerly when it is constant-evaluated;
// that path expanded folds only with several template packs, and it did
// not record an empty NON-type pack as empty (it read the identifier of a
// type parameter), so the fold reached the fallback that makes it `true'.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr int count()
{
  return 0;
}
template <class... T>
constexpr int count(int, T... t)
{
  return 1 + count(t...);
}

template <class... T>
struct S
{
  template <int... Is>
  static constexpr int f()
  {
    return 10 + count(Is...);
  }
  template <int... Is>
  static constexpr int g()
  {
    return (100 + ... + Is);
  }
};

struct P
{
  template <int... Is>
  static constexpr int g()
  {
    return (100 + ... + Is);
  }
};

static_assert(S<int>::f<>() == 10, "empty pack call");
static_assert(S<int>::f<1, 2>() == 12, "pack call");
static_assert(S<int>::g<>() == 100, "empty fold");
static_assert(S<int>::g<1, 2>() == 103, "fold");
static_assert(P::g<>() == 100, "empty fold, class");
static_assert(P::g<1, 2>() == 103, "fold, class");

int main()
{
  constexpr int b = S<int>::g<3>();
  __CPROVER_assert(b == 103, "constant");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
