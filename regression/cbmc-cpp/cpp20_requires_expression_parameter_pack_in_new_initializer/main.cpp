extern "C" void __CPROVER_assert(bool, const char *);
#include <new>

namespace ns
{
template <class T>
struct rr
{
  using type = T;
};
template <class T>
struct rr<T &>
{
  using type = T;
};
template <class T>
constexpr T &&forward(typename rr<T>::type &t) noexcept
{
  return static_cast<T &&>(t);
}
template <class T>
constexpr T *addressof(T &v) noexcept
{
  return __builtin_addressof(v);
}
constexpr bool is_constant_evaluated() noexcept
{
  return __builtin_is_constant_evaluated();
}
// N5008 [expr.prim.req.general]/4: the requires-expression's parameters
// (a pack among them) are in scope in its requirements
template <class T, class... Types>
requires requires(T *loc, Types &&..._Args)
{
  ::new(static_cast<void *>(loc)) T(forward<Types>(_Args)...);
}
constexpr T *construct_at(T *const loc, Types &&..._Args)
{
  return ::new(static_cast<void *>(loc)) T(forward<Types>(_Args)...);
}
// N5008 [temp.variadic]/5: the pack expansion forward<Types>(args)...
// in both branches, with T a pointer type and Types = {T &}
template <class T, class... Types>
constexpr void construct_in_place(T &obj, Types &&...args)
{
  if(::ns::is_constant_evaluated())
  {
    ::ns::construct_at(::ns::addressof(obj), ::ns::forward<Types>(args)...);
  }
  else
  {
    ::new(static_cast<void *>(::ns::addressof(obj)))
      T(::ns::forward<Types>(args)...);
  }
}
} // namespace ns
struct node
{
  int v;
};
int main()
{
  node n{4};
  node *src = &n;
  node *dst = nullptr;
  ns::construct_in_place(dst, src);
  __CPROVER_assert(dst == &n && dst->v == 4, "pointer constructed in place");
  __CPROVER_assert(dst == nullptr, "WRONG (must FAIL)");
  return 0;
}
