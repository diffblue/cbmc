// Test that std::swap works with multiple different types in the
// same function body when <sstream> (or <vector>) is included.
// This exercises:
// 1. Variadic template alias pack expansion (_Require<_Cond...>)
// 2. struct_tag expression resolution for ::value access
#include <sstream>
#include <utility>

struct BigInt
{
  unsigned size;
  unsigned *digit;
  void swap_self(BigInt &other)
  {
    std::swap(digit, other.digit);
    std::swap(size, other.size);
  }
};

int main()
{
  BigInt a, b;
  a.size = 1;
  b.size = 2;
  a.swap_self(b);
  __CPROVER_assert(a.size == 2, "swap worked");
  return 0;
}
