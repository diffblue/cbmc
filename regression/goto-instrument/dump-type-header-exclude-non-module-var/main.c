#include "main.h"

struct B
{
  int t;
  int g;
};

#define temperature(x) x.t

int main()
{
  struct B aStruct = {3, 8};
  __CPROVER_assert(my_config.a == 7, "Should be valid");
  my_config.a = nondet_int();

  __CPROVER_assert(!(my_config.a == 4), "Should be nondet now");
  __CPROVER_assert(aStruct.t, "Should not be null");
  __CPROVER_assert(temperature(aStruct) == 3, "Trying the macro");
}
