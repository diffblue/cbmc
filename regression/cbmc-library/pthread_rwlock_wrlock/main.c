#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_rwlock_wrlock();
  assert(0);
  return 0;
}
