// C++11 static constexpr auto member type deduction
struct S
{
  static constexpr auto value = 42;
};

template <auto V>
struct Wrap
{
  static constexpr auto val = V;
};

int main()
{
  __CPROVER_assert(S::value == 42, "static constexpr auto");
  __CPROVER_assert(Wrap<10>::val == 10, "auto nttp struct");
  return 0;
}
