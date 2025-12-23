#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_exit();
  assert(0);
  return 0;
}
