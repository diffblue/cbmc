#include <cassert>

struct S
{
};
struct F final
{
};
enum E
{
  A
};

int main()
{
  assert(__is_class(S));
  assert(!__is_class(int));
  assert(__is_enum(E));
  assert(!__is_enum(int));
  assert(__is_final(F));
  assert(!__is_final(S));
  return 0;
}
