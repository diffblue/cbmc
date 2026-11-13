// N5008 [expr.prim.fold]: folds over a type parameter pack in variable
// templates and in function templates without a function parameter pack
// (C++17 folds; C++14 variable templates).
extern "C" void __CPROVER_assert(bool, const char *);

template <typename T, typename... Ts>
constexpr bool has_v = (__is_same(T, Ts) || ...);

template <typename T, typename... Ts>
constexpr bool has_f()
{
  return (__is_same(T, Ts) || ...);
}

template <typename T, typename... Ts>
constexpr int count_f()
{
  return (__is_same(T, Ts) + ...);
}

template <typename... Ts>
constexpr int sizes_f()
{
  return (sizeof(Ts) + ...);
}

template <typename T, typename... Ts>
constexpr int count_left()
{
  return (0 + ... + __is_same(T, Ts));
}

struct N
{
  template <typename T>
  static constexpr bool contains = has_v<T, int, double>;
};

template <typename... Types>
struct S
{
  template <typename T>
  static constexpr bool contains = has_v<T, Types...>;
};

int main()
{
  __CPROVER_assert(has_v<int, int, double>, "has_v int");
  __CPROVER_assert(!has_v<char, int, double>, "has_v char");
  __CPROVER_assert(has_f<int, int, double>(), "has_f int");
  __CPROVER_assert(!has_f<char, int, double>(), "has_f char");
  __CPROVER_assert(count_f<char, int, double>() == 0, "count 0");
  __CPROVER_assert(count_f<double, int, double, double>() == 2, "count 2");
  __CPROVER_assert(count_left<double, int, double, double>() == 2, "left");
  __CPROVER_assert(sizes_f<char, int, double>() == 13, "sizes");
  __CPROVER_assert(N::contains<int>, "N int");
  __CPROVER_assert(!N::contains<char>, "N char");
  __CPROVER_assert(S<int, double>::contains<int>, "S int");
  __CPROVER_assert(!S<int, double>::contains<char>, "S char");
  return 0;
}
