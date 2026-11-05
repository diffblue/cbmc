// N5008 [over.match.class.deduct], [over.match.list]: vector<int> deduced from
// a braced list.
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector v{1, 2, 3};
  __CPROVER_assert(v.size() == 3, "vector<int> deduced from a braced list");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
