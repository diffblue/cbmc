// N5008 [temp.friend]/1: a friend declaration whose declarator-id is a
// template-id naming a specialization of a function template declared in
// another namespace (`friend constexpr partial cat::make<partial>(cat::ord)
// noexcept;') befriends that specialization and declares nothing; the
// specialization may then call the private constructor.  The shape of
// libstdc++ 16's <compare> (partial_ordering and __cmp_cat::__make).  The
// front end created an unrelated weak function symbol named after the
// template-id instead, the real specialization was not a friend, its body
// was dropped ("member 'partial::partial(...)' is not accessible") and the
// conversion returned nondet.
extern "C" void __CPROVER_assert(bool, const char *);
namespace cat
{
enum class ord : signed char
{
  equivalent = 0,
  less = -1,
  greater = 1
};
template <typename O>
constexpr ord ordv(O o) noexcept
{
  return ord(o.v);
}
template <typename O>
constexpr O make(ord o) noexcept
{
  return O(o);
}
} // namespace cat
class partial
{
  constexpr explicit partial(cat::ord o) noexcept
    : v(static_cast<signed char>(o))
  {
  }
  friend constexpr cat::ord cat::ordv<partial>(partial) noexcept;
  friend constexpr partial cat::make<partial>(cat::ord) noexcept;

public:
  signed char v;
  static const partial less;
};
class strong
{
  constexpr explicit strong(cat::ord o) noexcept
    : v(static_cast<signed char>(o))
  {
  }
  friend constexpr cat::ord cat::ordv<strong>(strong) noexcept;
  friend constexpr strong cat::make<strong>(cat::ord) noexcept;

public:
  signed char v;
  constexpr operator partial() const noexcept
  {
    return cat::make<partial>(cat::ord(v));
  }
  static const strong greater;
};
inline constexpr partial partial::less(cat::ord::less);
inline constexpr strong strong::greater(cat::ord::greater);
bool is_lt(partial p)
{
  return p.v < 0;
}
int main()
{
  partial p = strong::greater;
  __CPROVER_assert(
    p.v == 1, "conversion through befriended template specialization");
  __CPROVER_assert(!is_lt(strong::greater), "strong to partial at call");
  __CPROVER_assert(
    cat::ordv(strong::greater) == cat::ord::greater,
    "befriended ordv specialization");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
