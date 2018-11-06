#include <assert.h>
#include <threads.h>

int main()
{
  thrd_current();
  assert(0);
  return 0;
}
