#include <cassert>
#include <cstddef>
unsigned long long operator""_kb(unsigned long long x)
{
  return x * 1024;
}
int main()
{
  auto sz = 4_kb;
  assert(sz == 4096);
  return 0;
}
