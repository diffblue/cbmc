// N5008 [over.match.class.deduct], [vector.overview]: vector deduced from an
// iterator pair.
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector<int> a{1, 2, 3};
  std::vector v(a.begin(), a.end());
  __CPROVER_assert(v.size() == 3, "vector deduced from an iterator pair");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
