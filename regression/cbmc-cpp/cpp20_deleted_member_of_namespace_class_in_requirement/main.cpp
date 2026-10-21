extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.fct.def.delete]/2, [expr.prim.req.general]/5: the deleted
// fallback `operator()(auto &&) = delete' of a customization point object
// in a namespace is selected for E, and its use makes the requirement
// unsatisfied (libc++'s ranges::begin, behind ranges::range and so
// `arr | views::take(3)')
namespace rg
{
namespace b_
{
template <class T>
concept member_begin = requires(T && t)
{
  t.begin();
};
void begin() = delete;
template <class T>
concept unq_begin = !member_begin<T> && requires(T && t)
{
  begin(t);
};
struct fn
{
  template <class T, unsigned long N>
  constexpr auto operator()(T (&t)[N]) const noexcept requires(sizeof(T) >= 0)
  {
    return t + 0;
  }
  template <class T>
  requires member_begin<T> constexpr auto operator()(T &&t) const
  {
    return t.begin();
  }
  template <class T>
  requires unq_begin<T> constexpr auto operator()(T &&t) const
  {
    return begin(t);
  }
  void operator()(auto &&) const = delete;
};
} // namespace b_
inline namespace cpo
{
inline constexpr auto begin = b_::fn{};
}
} // namespace rg
template <class T>
concept has_begin = requires(T & t)
{
  rg::begin(t);
};
struct R
{
  int *begin()
  {
    return nullptr;
  }
};
struct E
{
};
int main()
{
  int a[2];
  __CPROVER_assert(has_begin<R> && has_begin<int[2]>, "ranges");
  __CPROVER_assert(!has_begin<E>, "deleted fallback");
  __CPROVER_assert(rg::begin(a) == a, "array");
  __CPROVER_assert(has_begin<E>, "WRONG (must FAIL)");
}
