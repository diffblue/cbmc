#include <assert.h>

int global = 10;
const int constant_global = 10;

void touches_globals(void);

int main(void)
{
  touches_globals();
  assert(global == 10);
  assert(constant_global == 10);
}
