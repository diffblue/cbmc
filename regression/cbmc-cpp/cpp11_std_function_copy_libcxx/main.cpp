extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
// N5008 [func.wrap.func.con]/4: the copy of a std::function holds a copy
// of the target.  libc++ clones the target through the virtual
// `__clone(__base *) const', declared with an unnamed parameter.
int one()
{
  return 1;
}
int main()
{
  std::function<int()> a = one;
  std::function<int()> b(a);
  __CPROVER_assert(b() == 1, "copy calls the target");
  __CPROVER_assert(b() == 2, "WRONG (must FAIL)");
  return 0;
}
