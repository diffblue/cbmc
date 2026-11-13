#include <assert.h>
#include <errno.h>
#include <semaphore.h>

// sem_trywait may fail with EAGAIN (POSIX.1-2017 sem_trywait).
int main(void)
{
  sem_t s;
  sem_init(&s, 0, 0);
  int r = sem_trywait(&s);
  // The call may return -1 with errno==EAGAIN, so r==0 is not guaranteed.
  assert(r == 0);
  return 0;
}
