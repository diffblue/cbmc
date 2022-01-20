#include <assert.h>

#ifndef __GNUC__
_Bool __atomic_always_lock_free(__CPROVER_size_t, void *);
#endif

int main()
{
  assert(__atomic_always_lock_free(sizeof(int), 0));
  return 0;
}
