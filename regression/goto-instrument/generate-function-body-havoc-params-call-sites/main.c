#include <string.h>

struct S
{
  int i;
  char *j;
};

void touches_parameter(
  int *param,
  int *const_param,
  struct S *struct_param,
  int non_pointer_param);

int main(void)
{
  int parameter = 10;
  int unchanged_parameter = 10;
  struct S my_struct = {.i = 10, .j = "10"};
  touches_parameter(&parameter, &unchanged_parameter, &my_struct, 4);
  __CPROVER_assert(parameter == 10, "assertion parameter == 10");
  __CPROVER_assert(
    unchanged_parameter == 10, "assertion unchanged_parameter == 10");
  __CPROVER_assert(my_struct.i == 10, "assertion my_struct.i == 10");
  __CPROVER_assert(
    strncmp(my_struct.j, "10", 3) == 0, "assertion my_struct.j == \"10\"");

  parameter = 10;
  unchanged_parameter = 10;
  my_struct.i = 10;
  my_struct.j = "10";
  touches_parameter(&parameter, &unchanged_parameter, &my_struct, 4);
  __CPROVER_assert(parameter == 10, "assertion parameter == 10");
  __CPROVER_assert(
    unchanged_parameter == 10, "assertion unchanged_parameter == 10");
  __CPROVER_assert(my_struct.i == 10, "assertion my_struct.i == 10");
  __CPROVER_assert(
    strncmp(my_struct.j, "10", 3) == 0, "assertion my_struct.j == \"10\"");
}
