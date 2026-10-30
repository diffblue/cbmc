#include <cassert>
void f() noexcept
{
}
void g()
{
}
int main()
{
  void (*fp)() noexcept = f;
  (void)fp;
  return 0;
}
