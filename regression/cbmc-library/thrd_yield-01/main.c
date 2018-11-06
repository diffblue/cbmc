#include <assert.h>
#include <threads.h>

int main()
{
  thrd_yield();
  assert(0);
  return 0;
}
