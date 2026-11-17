// N5008 [inplace.vector]: full at its capacity.
#include <inplace_vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::inplace_vector<int, 2> v;
  v.push_back(1);
  v.push_back(2);
  __CPROVER_assert(
    v.size() == 2 && !v.try_push_back(3), "full at its capacity");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
