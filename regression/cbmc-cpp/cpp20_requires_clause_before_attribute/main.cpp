// N5008 [temp.pre]/1: `template-head requires-clause declaration'; the
// declaration may begin with an attribute-specifier-seq ([dcl.attr.grammar]),
// and a GNU `__attribute__((...))' is one in the GNU dialect.  The parser
// accepted its parse of the requires-clause only when the next token began a
// decl-specifier or a name; `__attribute__' was not on the list, so the
// clause fell back to an atom COUNT and the constraint was never evaluated:
// overloads differing only in their requires-clause all stayed viable and
// the first declared won -- a wrong verdict.  This is libc++'s shape for
// every function (`[[nodiscard]] _LIBCPP_HIDE_FROM_ABI constexpr ...'), so
// its ranges customization-point objects (ranges::iter_move, ranges::begin,
// ranges::data) resolved to their first operator() for every argument.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept IsInt = __is_same(T, int);
template <class T>
concept IsDbl = __is_same(T, double);
struct fn
{
  template <class T>
  requires IsInt<T> [[nodiscard]] __attribute__((
    __visibility__("hidden"))) constexpr int
  operator()(T) const noexcept(noexcept(1))
  {
    return 1;
  }
  template <class T>
  requires IsDbl<T> [[nodiscard]] __attribute__((
    __visibility__("hidden"))) constexpr int
  operator()(T) const noexcept(noexcept(1))
  {
    return 2;
  }
};
template <class T>
requires IsInt<T> [[nodiscard]] __attribute__((__visibility__("hidden"))) int
g(T)
{
  return 1;
}
template <class T>
requires IsDbl<T> [[nodiscard]] __attribute__((__visibility__("hidden"))) int
g(T)
{
  return 2;
}
int main()
{
  __CPROVER_assert(fn{}(1) == 1 && fn{}(1.0) == 2, "member");
  __CPROVER_assert(g(1) == 1 && g(1.0) == 2, "free");
  __CPROVER_assert(g(1.0) == 1, "WRONG (must FAIL)");
}
