// N5008 [expr.unary.op]/3, [basic.stc.static]/1: a constexpr variable at
// namespace or class scope is an object with static storage duration;
// taking its address gives a pointer to that object, initialized with its
// value, also when the initializer is not a literal.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr long width = sizeof(long);
struct S
{
  static constexpr int k = 5;
};
// before C++17 an odr-used static constexpr member needs a definition
// ([class.static.data]/4 of C++14)
constexpr int S::k;
template <class T>
constexpr int size_of = sizeof(T);

int main()
{
  const long *p = &width;
  const int *q = &S::k;
  const int *r = &size_of<short>;
  __CPROVER_assert(*p == sizeof(long), "namespace scope");
  __CPROVER_assert(*q == 5, "static data member");
  __CPROVER_assert(*r == sizeof(short), "variable template (C++14)");
  __CPROVER_assert(*p == 0, "WRONG (must FAIL)");
  return 0;
}
