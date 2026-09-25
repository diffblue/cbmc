// C++17 structured bindings with tuple-like type
namespace std
{
template <class T>
struct tuple_size;
template <unsigned long I, class T>
struct tuple_element;
} // namespace std
struct Pair
{
  int a, b;
};
namespace std
{
template <>
struct tuple_size<Pair>
{
  static constexpr unsigned long value = 2;
};
template <>
struct tuple_element<0, Pair>
{
  using type = int;
};
template <>
struct tuple_element<1, Pair>
{
  using type = int;
};
} // namespace std
template <unsigned long I>
int get(const Pair &p);
template <>
int get<0>(const Pair &p)
{
  return p.a;
}
template <>
int get<1>(const Pair &p)
{
  return p.b;
}
int main()
{
  Pair p{10, 20};
  auto [x, y] = p;
  __CPROVER_assert(x == 10, "first");
  __CPROVER_assert(y == 20, "second");
  return 0;
}
