// N5008 [temp.constr.decl]/1, [temp.res.general]/1: names in a
// requires-clause are looked up from the template's declaration context, not
// from the call site.
extern "C" void __CPROVER_assert(bool, const char *);
#include <concepts>
#include <utility>

namespace ad
{
template <typename Adaptor, typename... Args>
concept adaptor_invocable = requires
{
  std::declval<Adaptor>()(std::declval<Args>()...);
};

struct closure
{
  // `closure` and `adaptor_invocable` are unqualified: visible from the
  // class and namespace ad, not from main()
  template <typename Self, typename Range>
  requires std::derived_from<std::remove_cvref_t<Self>, closure> &&
    adaptor_invocable<Self, Range> friend constexpr auto
    operator|(Range &&r, Self &&self)
  {
    return std::forward<Self>(self)(std::forward<Range>(r));
  }
};

struct sum_fn : closure
{
  template <typename R>
  constexpr int operator()(R &&r) const
  {
    int s = 0;
    for(auto x : r)
      s += x;
    return s;
  }
};
inline constexpr sum_fn sum{};
} // namespace ad

int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  int s = arr | ad::sum;
  __CPROVER_assert(s == 15, "pipe into hidden friend");
  __CPROVER_assert(s == 16, "WRONG (must FAIL)");
  return 0;
}
