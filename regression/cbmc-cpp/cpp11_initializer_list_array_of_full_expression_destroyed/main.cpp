// N5008 [dcl.init.list]/6 (Example 12): a backing array that does not
// initialize an initializer_list variable has the lifetime of a temporary
// and is destroyed at the end of the full-expression ([class.temporary]/4),
// here after the call of sum and after the initialization of v.
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
#include <vector>
int dtors = 0;
struct T
{
  int v;
  T(int x) : v(x)
  {
  }
  T(const T &o) : v(o.v)
  {
  }
  ~T()
  {
    ++dtors;
  }
};
int sum(std::initializer_list<T> l)
{
  int s = 0;
  for(const T &t : l)
    s += t.v;
  return s;
}
int main()
{
  int s = sum({T(3), T(4)});
  __CPROVER_assert(s == 7 && dtors == 2, "argument array destroyed");
  dtors = 0;
  {
    std::vector<T> v = {T(5), T(6)};
    __CPROVER_assert(dtors == 2, "array destroyed after initialization");
  }
  __CPROVER_assert(dtors == 4, "vector elements destroyed");
  __CPROVER_assert(dtors == 5, "WRONG (must FAIL)");
  return 0;
}
