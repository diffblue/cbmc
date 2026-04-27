// Concept used as boolean value in template argument
template <class T>
concept is_int = __is_same(T, int);

template <bool B, class T, class F>
struct If
{
  using type = F;
};
template <class T, class F>
struct If<true, T, F>
{
  using type = T;
};

template <class T>
struct S
{
  using type = typename If<is_int<T>, int, double>::type;
};

int main()
{
  __CPROVER_assert(__is_same(S<int>::type, int), "int satisfies is_int");
  __CPROVER_assert(
    __is_same(S<double>::type, double), "double does not satisfy is_int");
}
