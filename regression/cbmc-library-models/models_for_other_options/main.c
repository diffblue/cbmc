#include <string.h>

int main()
{
  // the models were preprocessed for other options: strlen.i is not used
  __CPROVER_assert(strlen("ab") == 2, "the built-in model is used");
  __CPROVER_assert(strlen("ab") == 42, "WRONG (must FAIL)");
  return 0;
}
