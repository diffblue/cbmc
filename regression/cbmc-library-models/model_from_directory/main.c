#include <string.h>

int main()
{
  // strlen.i in this directory replaces the dumped model of strlen
  __CPROVER_assert(strlen("ab") == 42, "the model of the directory is used");
  __CPROVER_assert(strlen("ab") == 2, "WRONG (must FAIL)");
  return 0;
}
