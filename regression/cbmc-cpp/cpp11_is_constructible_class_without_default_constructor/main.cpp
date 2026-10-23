extern "C" void __CPROVER_assert(bool, const char *);
struct no_default
{
  int x;
  no_default(int v) : x(v)
  {
  }
};
struct implicit_default
{
  int x;
};
struct deleted_default
{
  deleted_default() = delete;
};
template <class T>
struct wrap
{
  static constexpr bool value = __is_constructible(T);
};
// N5008 [meta.unary.prop]/9: is_constructible<T> holds iff `T t;' is
// well-formed
static_assert(!__is_constructible(no_default), "no default constructor");
static_assert(__is_constructible(no_default, int), "from int");
static_assert(__is_constructible(implicit_default), "implicit default");
static_assert(!__is_constructible(deleted_default), "deleted default");
static_assert(!wrap<no_default>::value, "through a template");
int main()
{
  bool b = __is_constructible(no_default);
  __CPROVER_assert(!b, "no default constructor at run time");
  __CPROVER_assert(b, "WRONG (must FAIL)");
}
