#include <assert.h>
#include <pthread_lib.h>

int main()
{
  _pthread_join();
  assert(0);
  return 0;
}
