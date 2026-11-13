// N5008 [temp.constr.decl]/3.3: the type-constraint `has_begin T' is
// checked before the requires-clause, and an unsatisfied one leaves it
// uninstantiated: kind<int>, whose initializer is ill-formed, is never
// instantiated.  The front end evaluated the requires-clause of the partial
// specialization first while it chose a specialization.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept has_begin = requires(T t) { t.begin(); };
template <class T>
constexpr auto kind = []
{
  static_assert(sizeof(T) == 0, "primary template of kind");
  return 1;
}();
template <class T, class C>
struct fmt
{
  static constexpr int v = 0;
};
template <has_begin T, class C>
  requires(kind<T> != 2 && sizeof(C) == 1)
struct fmt<T, C>
{
  static constexpr int v = 1;
};
struct range
{
  int *begin();
};
template <>
constexpr auto kind<range> = 1;
int main()
{
  __CPROVER_assert(fmt<int, char>::v == 0, "primary template");
  __CPROVER_assert(fmt<range, char>::v == 1, "partial specialization");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
