// N5008 [container.reqmts]/25: the destructor of a container destroys
// every element; libstdc++'s vector does so through std::_Destroy.
extern "C" void __CPROVER_assert(bool, const char *);
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
int main()
{
  {
    std::vector<T> v;
    v.reserve(2);
    v.emplace_back(5);
    v.emplace_back(6);
    __CPROVER_assert(v.size() == 2, "size");
  }
  __CPROVER_assert(dtors == 2, "elements destroyed");
  __CPROVER_assert(dtors == 0, "WRONG (must FAIL)");
  return 0;
}
