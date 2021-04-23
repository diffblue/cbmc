#include <assert.h>

#pragma pack(push, 1)
struct S
{
  int a[2];
  int x;
};
#pragma pack(pop)

#ifdef _MSC_VER
#  define _Static_assert(x, m) static_assert(x, m)
#endif

int main()
{
  int A[3];
  _Static_assert(sizeof(A) == sizeof(struct S), "");
  struct S *s = A;
  A[2] = 42;
  assert(s->a[2] == 42);
}
