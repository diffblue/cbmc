#if __has_include(<numbers>)
// C++20 std::numbers
#  include <numbers>
int main()
{
  constexpr double pi = std::numbers::pi;
  __CPROVER_assert(pi > 3.14 && pi < 3.15, "pi");
}

#else
int main()
{
}
#endif
