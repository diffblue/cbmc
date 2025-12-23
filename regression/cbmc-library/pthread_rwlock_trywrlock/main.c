#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_rwlock_trywrlock();
  assert(0);
  return 0;
}
