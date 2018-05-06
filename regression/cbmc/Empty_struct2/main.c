#include <assert.h>

struct empty
{
};

#pragma pack(1)
struct S
{
  char x;
  struct empty e;
  char y;
};
#pragma pack()

int main()
{
  struct S s;
  assert(sizeof(struct S) == 2);

  struct empty *p = &s.e;

  assert(p == (char *)&s + 1);

  return 0;
}
