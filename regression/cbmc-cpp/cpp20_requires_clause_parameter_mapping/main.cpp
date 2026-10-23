// N5008 [temp.constr.decl]/3, [temp.constr.atomic]/1: a requires-clause is
// checked with the constrained declaration's parameter mapping -- packs in
// concept-ids and folds, non-type arguments, the enclosing class template's
// parameters, names dependent on them.
extern "C" void __CPROVER_assert(bool, const char *);
template <typename... Ts>
concept all_small = ((sizeof(Ts) <= 4) && ...);
template <typename T, typename... Rest>
concept first_is = (__is_same(T, Rest) || ...);
template <int N, typename... Ts>
concept arity = (sizeof...(Ts) == N);

template <typename... Args>
requires all_small<Args...> constexpr int f(Args...)
{
  return 1;
}
template <typename... Args>
constexpr int f(Args...)
{
  return 2;
}

template <typename T, typename... Args>
requires first_is<T, Args...> constexpr int g(T, Args...)
{
  return 1;
}
template <typename T, typename... Args>
constexpr int g(T, Args...)
{
  return 2;
}

template <typename... Args>
requires arity<3, Args...> constexpr int h(Args...)
{
  return 1;
}
template <typename... Args>
constexpr int h(Args...)
{
  return 2;
}

template <typename T>
struct box
{
  using value_type = T;
  template <typename U>
  requires __is_same(U, typename box<T>::value_type) constexpr int same(U) const
  {
    return 1;
  }
  template <typename U>
  constexpr int same(U) const
  {
    return 2;
  }
};

int main()
{
  __CPROVER_assert(f(1, 'c') == 1, "all small");
  __CPROVER_assert(f(1, 2.0) == 2, "double is not small");
  __CPROVER_assert(g(1, 2.0, 3) == 1, "int among the rest");
  __CPROVER_assert(g(1, 2.0, 'c') == 2, "int not among the rest");
  __CPROVER_assert(h(1, 2, 3) == 1, "three");
  __CPROVER_assert(h(1, 2) == 2, "two");
  box<int> b;
  __CPROVER_assert(b.same(1) == 1, "U is value_type");
  __CPROVER_assert(b.same(1.0) == 2, "U is not value_type");
  __CPROVER_assert(f(1, 'c') + h(1, 2) == 3, "values");
  __CPROVER_assert(g(1, 2.0, 'c') == 1, "WRONG (must FAIL)");
  return 0;
}
