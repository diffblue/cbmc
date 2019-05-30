#include <assert.h>

int main()
{
  assert(__atomic_always_lock_free(sizeof(int), 0));
  return 0;
}
