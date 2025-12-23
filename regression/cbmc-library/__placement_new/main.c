#include <assert.h>
#include <new.h>

int main()
{
  __placement_new();
  assert(0);
  return 0;
}
