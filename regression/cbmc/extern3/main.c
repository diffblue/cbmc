#include <assert.h>

extern int x;

int main(int argc, char *argv[])
{
  if(argc > 5)
    x = 42;

  __CPROVER_assert(x == 42, "should fail");
}
