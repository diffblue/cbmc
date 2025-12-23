#include <assert.h>
#include <semaphore.h>

int main()
{
  sem_post();
  assert(0);
  return 0;
}
