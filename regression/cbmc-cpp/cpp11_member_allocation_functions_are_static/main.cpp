#include <cstddef>
extern "C" void __CPROVER_assert(bool, const char *);
static char arena[64];
struct C
{
  int y;
  void *operator new(std::size_t n)
  {
    return arena + 8;
  }
  void *operator new[](std::size_t n)
  {
    return arena + 16;
  }
  void operator delete(void *p)
  {
  }
};
struct D : C
{
  int z;
};
int main()
{
  void *a = C::operator new(4);
  void *b = D::operator new(4);
  void *c = C::operator new[](4);
  __CPROVER_assert(a == arena + 8 && b == a && c == arena + 16, "direct calls");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
