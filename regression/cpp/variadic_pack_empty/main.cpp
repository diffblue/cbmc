// Variadic template aliases with empty parameter packs.

template <bool B>
struct bool_constant
{
  static const bool value = B;
};

typedef bool_constant<true> true_type;
typedef bool_constant<false> false_type;

template <typename _Tp, typename... _Args>
using is_constructible_impl = bool_constant<true>;

template <typename _Tp>
struct is_default_constructible : is_constructible_impl<_Tp>
{
};

is_default_constructible<int> x;

int main()
{
  return 0;
}
