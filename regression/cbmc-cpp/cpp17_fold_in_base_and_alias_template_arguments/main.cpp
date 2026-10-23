// N5008 [expr.prim.fold]/2,3, [temp.variadic]/5: a fold over a class
// template's pack may appear in a base-specifier's or an alias member's
// template arguments; it expands like a fold in the class body.  Over a
// one-element pack it is the single pattern instance.  libc++'s tuple
// constraints (_And over is_constructible<_Tp, _Up>...) are written this way.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool B>
struct bc
{
  static constexpr bool value = B;
};

template <class... P>
struct all_of : bc<(P::value && ...)>
{
};

template <class... P>
struct any_of : bc<(P::value || ...)>
{
};

template <int... N>
struct sum_is_3 : bc<((N + ...) == 3)>
{
};

template <class... P>
struct alias_of
{
  using type = bc<(P::value && ...)>;
};

static_assert(!all_of<bc<false>>::value);
static_assert(all_of<bc<true>>::value && all_of<>::value);
static_assert(!all_of<bc<true>, bc<false>>::value);
static_assert(!any_of<bc<false>>::value && any_of<bc<false>, bc<true>>::value);
static_assert(sum_is_3<1, 2>::value && !sum_is_3<1, 1>::value);
static_assert(!alias_of<bc<false>>::type::value);
static_assert(alias_of<bc<true>, bc<true>>::type::value);

int main()
{
  __CPROVER_assert(!all_of<bc<false>>::value, "all_of");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
