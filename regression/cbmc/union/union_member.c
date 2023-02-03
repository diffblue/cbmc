#include <assert.h>

struct s
{
  union
  {
    char b[2];
  };
};

int main()
{
  struct s X;
  __CPROVER_assert(X.b[1] == 2, "should fail");
}
