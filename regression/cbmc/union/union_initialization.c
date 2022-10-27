#include <assert.h>

struct s
{
  union U
  {
    char c;
    char b[2];
  } u;
} X;

int main()
{
  // expected to fail
  __CPROVER_assert(X.u.b[1] == 2, "should fail");
}
