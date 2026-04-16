// Comma operator in non-type template arguments.
// libc++ __all<Pred...> uses this pattern.
template <bool...>
struct dummy
{
};
template <bool... Pred>
struct my_all
{
  static constexpr bool value =
    __is_same(dummy<Pred...>, dummy<((void)Pred, true)...>);
};
static_assert(my_all<true, true>::value, "all true");
int main()
{
}
