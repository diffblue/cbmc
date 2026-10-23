#include <tuple>
extern "C" void __CPROVER_assert(bool, const char *);
int add(int a, int b)
{
  return a + b;
}
static_assert(std::tuple_size<std::tuple<int, int>>::value == 2, "tuple_size");
static_assert(
  std::tuple_size_v<const std::tuple<int, char, int>> == 3,
  "const");
int main()
{
  auto t = std::make_tuple(1, 2);
  std::integral_constant<std::size_t, 2> *base =
    static_cast<std::tuple_size<std::tuple<int, int>> *>(nullptr);
  __CPROVER_assert(base == nullptr, "the base of the selected specialization");
  __CPROVER_assert(std::apply(add, t) == 3, "std::apply");
  __CPROVER_assert(std::apply(add, t) == 4, "WRONG (must FAIL)");
}
