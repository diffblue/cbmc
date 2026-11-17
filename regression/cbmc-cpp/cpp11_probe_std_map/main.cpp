// N5008 [map]: std::map insertion and ordering.
#include <map>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::map<int, int> m;
  m[2] = 5;
  m[1] = 3;
  __CPROVER_assert(m.size() == 2 && m.begin()->second == 3, "map ordering");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
