// N5008 [dcl.init.list]/6, [class.temporary]/6, [stmt.jump.general]/2: the
// backing array of an initializer_list variable lives as long as the
// variable; it is destroyed at the end of each iteration, also when the loop
// is left by break.
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
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
int main()
{
  for(int i = 0; i < 3; ++i)
  {
    std::initializer_list<T> l = {T(1), T(2)};
    if(i == 1)
      break;
  }
  __CPROVER_assert(dtors == 4, "loop and break");
  __CPROVER_assert(dtors == 6, "WRONG (must FAIL)");
  return 0;
}
