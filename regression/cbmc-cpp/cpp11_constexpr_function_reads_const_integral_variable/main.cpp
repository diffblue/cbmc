extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.const]/8-9: a non-volatile const variable of integral or
// enumeration type initialized with a constant is usable in constant
// expressions, also when a constexpr function reads it
const int limit = 3;
enum class colour
{
  red,
  green
};
const colour favourite = colour::green;
constexpr int twice_limit()
{
  return 2 * limit;
}
constexpr bool is_green()
{
  return favourite == colour::green;
}
template <int N>
struct size
{
  static const int value = N;
};
static_assert(twice_limit() == 6, "static_assert");
int main()
{
  __CPROVER_assert(size<twice_limit()>::value == 6, "integral");
  __CPROVER_assert(size<is_green()>::value == 1, "enumeration");
  __CPROVER_assert(size<twice_limit()>::value == 3, "WRONG (must FAIL)");
  return 0;
}
