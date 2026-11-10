// N5008 [vector]: std::vector list-initialization and push_back.
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector<int> v{1, 2, 3};
  v.push_back(4);
  __CPROVER_assert(v.size() == 4 && v[3] == 4, "vector push_back");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
