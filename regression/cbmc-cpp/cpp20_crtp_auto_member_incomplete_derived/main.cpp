// N5008 [temp.inst]/4, [temp.point]/8: a member function of a class template
// specialization is instantiated when odr-used; a body that cannot be
// converted while the CRTP-derived class is still incomplete must not be
// dropped.
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
#include <utility>

namespace rg
{
struct begin_fn
{
  template <typename T>
  constexpr auto operator()(T &&t) const
  {
    if constexpr(std::is_array_v<std::remove_reference_t<T>>)
      return t + 0;
    else
      return t.begin();
  }
};
inline constexpr begin_fn begin{};

template <typename Derived>
struct view_interface
{
  constexpr Derived &derived()
  {
    return static_cast<Derived &>(*this);
  }
  // uses the derived class, which is incomplete while this base is
  // being instantiated for it
  constexpr auto front()
  {
    return *rg::begin(derived());
  }
  constexpr bool empty()
  {
    return rg::begin(derived()) == nullptr;
  }
};

template <typename R>
struct ref_view : view_interface<ref_view<R>>
{
  R *p;
  template <typename T>
  requires(!__is_same(T, ref_view)) constexpr ref_view(T &&t)
    : p(&static_cast<R &>(static_cast<T &&>(t)))
  {
  }
  constexpr auto begin() const
  {
    return rg::begin(*p);
  }
};
template <typename R>
ref_view(R &) -> ref_view<R>;
} // namespace rg

int main()
{
  int arr[] = {4, 5, 6};
  rg::ref_view rv{arr};
  auto b = rg::begin(rv);
  static_assert(__is_same(decltype(b), int *), "begin type through ref_view");
  __CPROVER_assert(*b == 4, "begin value");
  __CPROVER_assert(rv.front() == 4, "front through the CRTP base");
  __CPROVER_assert(!rv.empty(), "empty through the CRTP base");
  __CPROVER_assert(*b == 5, "WRONG (must FAIL)");
  return 0;
}
