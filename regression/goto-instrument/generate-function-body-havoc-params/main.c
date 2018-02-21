#include <assert.h>

void touches_parameter(int *param, const int *const_param);

int main(void)
{
  int parameter = 10;
  int constant_parameter = 10;
  touches_parameter(&parameter, &constant_parameter);
  assert(parameter == 10);
  assert(constant_parameter == 10);
}
