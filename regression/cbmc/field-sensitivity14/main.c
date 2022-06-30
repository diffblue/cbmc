#include <string.h>

struct S
{
  int x;
  int y;
};

int main()
{
  struct S s1, s2, s3;

  s1.y = 42;
  memcpy(&s2, &s1, sizeof(struct S));
  __CPROVER_assert(s2.y == 42, "should propagate");

  s3.x = 42;
  memcpy(&s2, &s3, sizeof(struct S));
  __CPROVER_assert(s2.x == 42, "should propagate");
}
