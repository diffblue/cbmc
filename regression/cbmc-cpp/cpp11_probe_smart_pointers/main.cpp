// N5008 [unique.ptr], [util.smartptr.shared]: std::unique_ptr,
// std::make_shared and use_count.
#include <memory>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto u = std::unique_ptr<int>(new int(3));
  auto s = std::make_shared<int>(4);
  auto t = s;
  __CPROVER_assert(*u == 3 && s.use_count() == 2, "unique_ptr and shared_ptr");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
