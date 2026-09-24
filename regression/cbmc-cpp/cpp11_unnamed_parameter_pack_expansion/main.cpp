// N5008 [temp.variadic]/5, [dcl.fct]/15: a function parameter pack need not
// be named; `Args...` expands to one parameter per deduced element exactly as
// `Args... a` does.
extern "C" void __CPROVER_assert(bool, const char *);

template <typename... Args>
constexpr int count(Args...)
{
  return sizeof...(Args);
}
template <typename... Args>
constexpr int count_ref(Args &&...)
{
  return sizeof...(Args);
}
template <typename T, typename... Args>
constexpr int after_first(T, Args...)
{
  return sizeof...(Args);
}
struct S
{
  template <typename... Args>
  constexpr int m(Args...) const
  {
    return sizeof...(Args) * 10;
  }
};
template <typename... Ts>
concept all_small = ((sizeof(Ts) <= 4) && ...);
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

int main()
{
  static_assert(count() == 0, "zero");
  static_assert(count(1) == 1, "one");
  static_assert(count(1, 'c', 2.0) == 3, "three");
  static_assert(count_ref(1, 2) == 2, "forwarding references");
  static_assert(after_first(1, 'a', 'b') == 2, "after a named parameter");
  constexpr S s;
  static_assert(s.m(1, 2) == 20, "member template");
  static_assert(f(1, 'c') == 1, "constrained variadic");
  static_assert(f(1, 2.0) == 2, "unconstrained twin");
  int i = 1;
  __CPROVER_assert(
    count(i, i) == 2 && count_ref(i, 2) == 2 && s.m(i) == 10, "runtime");
  __CPROVER_assert(count(i, i) == 3, "WRONG (must FAIL)");
  return 0;
}
