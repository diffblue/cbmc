#include <list>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::list<int> l;
  l.push_back(42);
  __CPROVER_assert(l.size() == 1, "one element");
  __CPROVER_assert(l.back() == 42, "its value");
  __CPROVER_assert(l.back() == 43, "WRONG (must FAIL)");
}
