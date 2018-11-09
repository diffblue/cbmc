#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_cond_signal();
  assert(0);
  return 0;
}
