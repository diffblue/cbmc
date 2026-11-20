// N5008 [dcl.init.list], [support.initlist]: a std::initializer_list
// parameter.
#include <initializer_list>
extern "C" void __CPROVER_assert(bool, const char *);
int sum(std::initializer_list<int> l)
{
  int s = 0;
  for(int x : l)
    s += x;
  return s;
}
int main()
{
  __CPROVER_assert(sum({1, 2, 3, 4}) == 10, "initializer_list");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
