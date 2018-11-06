#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_cond_broadcast();
  assert(0);
  return 0;
}
