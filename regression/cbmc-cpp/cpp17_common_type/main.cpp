// C++17: std::common_type with partial specialization empty pack matching
#include <type_traits>

int main()
{
  // common_type<T> matches the single-type specialization
  using T1 = std::common_type<int>::type;
  T1 x = 42;
  __CPROVER_assert(x == 42, "common_type<int>");

  // common_type<T1, T2> matches the two-type specialization
  using T2 = std::common_type<int, long>::type;
  T2 y = 100;
  __CPROVER_assert(y == 100, "common_type<int,long>");
}
