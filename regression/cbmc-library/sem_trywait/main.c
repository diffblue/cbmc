#include <assert.h>
#include <semaphore.h>

int main()
{
  sem_trywait();
  assert(0);
  return 0;
}
