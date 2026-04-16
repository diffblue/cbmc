// Comma operator in non-type template arguments is not evaluated.
// libc++ __all<Pred...> uses ((void)Pred, true)... which CBMC
// cannot evaluate as a constant expression.
template<bool...> struct dummy {};
template<bool... Pred>
struct my_all {
  static constexpr bool value =
    __is_same(dummy<Pred...>, dummy<((void)Pred, true)...>);
};
static_assert(my_all<true, true>::value, "all true");
static_assert(!my_all<true, false>::value, "not all true");
int main() {}
