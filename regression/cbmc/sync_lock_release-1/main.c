#include <stdint.h>

int main()
{
  int8_t *n;
  __sync_lock_release(n);
  int32_t *l;
  __sync_lock_release(l);
  return 0;
}
