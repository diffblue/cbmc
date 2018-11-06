#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_join();
  assert(0);
  return 0;
}
