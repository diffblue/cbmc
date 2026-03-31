// Requires GCC 13+ or Clang (older libstdc++ lacks support).
#if !defined(__GNUC__) && !defined(_MSC_VER) || defined(__clang__) || __GNUC__ >= 13
// C++23 std::unreachable
#  include <utility>
int f(int x)
{
  if(x > 0)
    return x;
  std::unreachable();
}
int main()
{
  __CPROVER_assert(f(42) == 42, "unreachable");
}
#else
int main()
{
}
#endif
