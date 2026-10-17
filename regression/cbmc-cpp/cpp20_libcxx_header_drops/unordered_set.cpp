#include <unordered_set>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::unordered_set<int> s;
  s.insert(5);
  s.insert(7);
  __CPROVER_assert(s.count(5) == 1 && s.count(6) == 0, "count");
  __CPROVER_assert(s.size() == 2, "size");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
