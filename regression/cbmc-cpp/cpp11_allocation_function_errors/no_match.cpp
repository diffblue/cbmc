#include <cstddef>
struct C
{
  void *operator new(std::size_t, int);
};
int main()
{
  // [expr.new]/13: the class scope declares an operator new, so the global
  // scope is not searched; none of the class's matches
  C *c = new C;
  (void)c;
  return 0;
}
