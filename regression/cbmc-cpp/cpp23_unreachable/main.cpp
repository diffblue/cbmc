// C++23 std::unreachable
#include <utility>
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
