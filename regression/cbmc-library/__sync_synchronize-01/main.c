#include <assert.h>
#include <gcc.h>

int main()
{
  __sync_synchronize();
  assert(0);
  return 0;
}
