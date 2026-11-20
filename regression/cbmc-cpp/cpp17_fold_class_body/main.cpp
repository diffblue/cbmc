// C++17: fold expressions in class template member initializers
template <bool... Bs>
struct AllTrue
{
  static constexpr bool value = (Bs && ...);
};

template <bool... Bs>
struct AnyTrue
{
  static constexpr bool value = (Bs || ...);
};

int main()
{
  __CPROVER_assert(AllTrue<true, true, true>::value, "all true");
  __CPROVER_assert(!AllTrue<true, false, true>::value, "not all true");
  __CPROVER_assert(AnyTrue<false, true, false>::value, "any true");
  __CPROVER_assert(!AnyTrue<false, false, false>::value, "none true");
}
