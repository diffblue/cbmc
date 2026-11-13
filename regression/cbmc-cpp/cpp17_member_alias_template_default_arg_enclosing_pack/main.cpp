// N5008 [temp.mem]/1: member alias template with a default argument that
// names the enclosing class template's parameter pack.
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;

template <size_t N, typename... Ts>
struct nth;
template <typename T0, typename... Ts>
struct nth<0, T0, Ts...>
{
  using type = T0;
};
template <size_t N, typename T0, typename... Ts>
struct nth<N, T0, Ts...> : nth<N - 1, Ts...>
{
};

template <bool B, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  using type = T;
};
template <bool B, typename T = void>
using enable_if_t = typename enable_if<B, T>::type;

template <typename... Types>
struct variant
{
  template <size_t N, typename = enable_if_t<(N < sizeof...(Types))>>
  using to_type = typename nth<N, Types...>::type;
  template <size_t N>
  using to_type2 = typename nth<N, Types...>::type;
  static constexpr size_t count = sizeof...(Types);
};

int main()
{
  using V = variant<int, double>;
  __CPROVER_assert(V::count == 2, "count");
  __CPROVER_assert(__is_same(V::to_type2<1>, double), "to_type2");
  __CPROVER_assert(__is_same(V::to_type<1>, double), "to_type");
  __CPROVER_assert(__is_same(V::to_type<0>, int), "to_type 0");
  return 0;
}
