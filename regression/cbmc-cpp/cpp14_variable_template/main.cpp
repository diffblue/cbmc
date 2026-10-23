// C++14 variable templates
template <typename T>
constexpr T pi = T(3);

int main()
{
  int x = pi<int>;
  __CPROVER_assert(x == 3, "variable template");
  return 0;
}
