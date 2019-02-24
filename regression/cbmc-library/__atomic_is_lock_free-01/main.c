#include <assert.h>

int main()
{
  assert(__atomic_is_lock_free(sizeof(int), 0));
  return 0;
}
