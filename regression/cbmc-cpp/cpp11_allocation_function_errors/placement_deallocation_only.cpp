#include <cstddef>
struct C
{
  void operator delete(void *, int);
};
int main()
{
  C *c = ::new C;
  // [expr.delete]/8: only placement deallocation functions in the class
  delete c;
  return 0;
}
