#include <assert.h>
#include <semaphore.h>

int main()
{
  sem_post_multiple();
  assert(0);
  return 0;
}
