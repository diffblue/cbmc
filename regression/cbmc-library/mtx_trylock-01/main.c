#include <assert.h>
#include <threads.h>

int main()
{
  mtx_trylock();
  assert(0);
  return 0;
}
