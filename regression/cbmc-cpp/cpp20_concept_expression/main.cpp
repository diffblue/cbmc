// C++20: concept used as boolean expression
template <typename T>
concept Integral = __is_same(T, int) || __is_same(T, long);

template <typename T>
int check()
{
  if constexpr(Integral<T>)
    return 1;
  else
    return 0;
}

int main()
{
  __CPROVER_assert(check<int>() == 1, "int is integral");
  __CPROVER_assert(check<double>() == 0, "double is not integral");

  // Concept as direct bool value
  bool b = Integral<int>;
  __CPROVER_assert(b, "concept as bool");
}
