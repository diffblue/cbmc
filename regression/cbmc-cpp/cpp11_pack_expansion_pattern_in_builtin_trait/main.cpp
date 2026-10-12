// N5008 [temp.variadic]/5: the pattern of a pack expansion in a type-trait
// argument list may be any type naming the pack: `__is_constructible(X,
// Y &&...)' expands to one argument Y_k && per element.  CBMC expanded only
// the bare `Y...' and treated `Y &&...' as a single argument.  libc++'s
// is_constructible_v<_Tp, _Args&&...> and __perfect_forward_impl's
// constructor constraint are written this way.
extern "C" void __CPROVER_assert(bool, const char *);

struct two
{
  two(int, char)
  {
  }
};

template <class X, class... Y>
struct constructible
{
  static constexpr bool by_value = __is_constructible(X, Y...);
  static constexpr bool by_rvalue = __is_constructible(X, Y &&...);
  static constexpr bool by_const_ref = __is_constructible(X, const Y &...);
};

static_assert(constructible<two, int, char>::by_value);
static_assert(constructible<two, int, char>::by_rvalue);
static_assert(constructible<two, int, char>::by_const_ref);
static_assert(!constructible<two, int>::by_rvalue);
static_assert(!constructible<two, int, char, int>::by_rvalue);

int main()
{
  __CPROVER_assert(constructible<two, int, char>::by_rvalue, "rvalue pattern");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
