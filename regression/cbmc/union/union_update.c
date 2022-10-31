#include <assert.h>

struct s
{
  char a;
  union U
  {
    char c;
    char b[2];
  } u;
} X = {1, 2};

int main()
{
  __CPROVER_assert(X.u.b[1] == 123, "should fail");
}
