// N5008 [dcl.init.list]/5: the backing array of an initializer_list has
// one element copy-initialized from each element of the braced list;
// [dcl.init.list]/6: the array has the lifetime of a temporary bound to
// the initializer_list object -- here the variable `kept', so its elements
// are destroyed at the end of the block.  The front end holds the elements
// in a static array that is never destroyed: the destructor count stays 0.
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
  {
    std::initializer_list<T> kept = {T(4), T(5)};
    __CPROVER_assert(kept.size() == 2, "size");
    __CPROVER_assert(dtors == 0, "no element destroyed yet");
    __CPROVER_assert(kept.begin()->v == 4, "element value");
  }
  __CPROVER_assert(dtors == 2, "destroyed with the variable");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
