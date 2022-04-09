#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>

int main()
{
  int notdet_int;
  int *ptr;
  bool notdet_bool;
  if(notdet_bool)
  {
    ptr = &notdet_int;
    assert(((uint64_t)ptr) > 1);
  }
  else
  {
    ptr = NULL;
  }
  assert(((uint64_t)ptr) != 0);
}
