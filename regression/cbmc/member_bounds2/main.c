#include <assert.h>

#pragma pack(push, 1)
struct SU
{
  union {
    int a[2];
  } u;
  int x;
};
#pragma pack(pop)

int main()
{
  struct SU su;
  su.u.a[2] = 42;
  assert(*((int *)&su + 2) == 42);
  assert(su.x == 42);
}
