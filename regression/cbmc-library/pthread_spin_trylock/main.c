#include <assert.h>
#include <pthread_lib.h>

int main()
{
  pthread_spin_trylock();
  assert(0);
  return 0;
}
