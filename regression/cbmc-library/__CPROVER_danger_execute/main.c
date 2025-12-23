#include <assert.h>
#include <cegis.h>

int main()
{
  __CPROVER_danger_execute();
  assert(0);
  return 0;
}
