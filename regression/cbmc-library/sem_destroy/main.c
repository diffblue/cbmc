#include <assert.h>
#include <semaphore.h>

int main()
{
  sem_destroy();
  assert(0);
  return 0;
}
