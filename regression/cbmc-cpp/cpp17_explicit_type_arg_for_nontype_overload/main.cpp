// N5008 [temp.arg]/2, [temp.deduct]/8: kind mismatch of an explicit
// template argument removes the candidate (std::get<T>(variant) vs
// std::get<N>(variant)).
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;

template <typename... Ts>
struct V
{
  int a;
  double b;
};

template <size_t N, typename... Ts>
int get(V<Ts...> &v)
{
  return N == 0 ? v.a : (int)v.b;
}

template <typename T, typename... Ts>
int get(V<Ts...> &v)
{
  constexpr size_t n = __is_same(T, int) ? 0 : 1;
  return get<n>(v);
}

int main()
{
  V<int, double> v{42, 2.5};
  __CPROVER_assert(get<1>(v) == 2, "by index");
  __CPROVER_assert(get<double>(v) == 2, "by type double");
  __CPROVER_assert(get<int>(v) == 42, "by type int");
  return 0;
}
