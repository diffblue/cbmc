#include <assert.h>

#pragma pack(push, 1)
struct S
{
  int a[2];
  int x;
};
#pragma pack(pop)

int main()
{
  int A[3];
  _Static_assert(sizeof(A) == sizeof(struct S), "");
  struct S *s = A;
  A[2] = 42;
  assert(s->a[2] == 42);
}
