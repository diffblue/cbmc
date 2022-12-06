#include <assert.h>
#include <time.h>

int main()
{
  pthread_key_delete();
  assert(0);
  return 0;
}
