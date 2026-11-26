#include <assert.h>
#include <semaphore.h>

// sem_getvalue must write *sval (POSIX.1-2017 sem_getvalue).
int main(void)
{
  sem_t s;
  sem_init(&s, 0, 3);
  int v = 7;
  sem_getvalue(&s, &v);
  // The model writes a nondeterministic non-negative value to v,
  // so v==7 is not guaranteed.
  assert(v == 7);
  return 0;
}
