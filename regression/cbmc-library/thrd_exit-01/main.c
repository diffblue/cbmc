#include <assert.h>
#include <threads.h>

int main()
{
  thrd_exit();
  assert(0);
  return 0;
}
