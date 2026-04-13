// libc++ std::any basic operations
#include <any>
int main()
{
  std::any a = 42;
  __CPROVER_assert(a.has_value(), "has_value");
}
