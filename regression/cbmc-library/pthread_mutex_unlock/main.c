#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_mutex_unlock();
  assert(0);
  return 0;
}
