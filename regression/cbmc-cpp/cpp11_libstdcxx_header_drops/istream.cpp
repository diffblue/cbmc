#include <istream>
extern "C" void __CPROVER_assert(bool, const char *);
void f(std::istream &i)
{
  char b[4];
  i.read(b, 4);
}
int main()
{
  __CPROVER_assert(true, "header");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
