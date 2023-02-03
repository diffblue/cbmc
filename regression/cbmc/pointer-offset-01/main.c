#include <assert.h>
#include <stdlib.h>

int main(void)
{
  size_t size;
  size_t max_malloc_size = __CPROVER_max_malloc_size;
  __CPROVER_assume(0 <= size && size <= max_malloc_size);
  char *lb = malloc(size);
  size_t offset_lb = __CPROVER_POINTER_OFFSET(lb);
  size_t object_lb = __CPROVER_POINTER_OBJECT(lb);

  char *ub = lb + size;
  size_t offset_ub = __CPROVER_POINTER_OFFSET(ub);
  size_t object_ub = __CPROVER_POINTER_OBJECT(ub);

  char *ubp1 = lb + size + 1;
  size_t offset_ubp1 = __CPROVER_POINTER_OFFSET(ubp1);
  size_t object_ubp1 = __CPROVER_POINTER_OBJECT(ubp1);

  assert(object_ub == object_lb);       // proved
  assert(object_ubp1 == object_lb);     // proved
  assert(ubp1 > ub);                    // proved
  assert(offset_ubp1 > offset_ub);      // proved
  assert(offset_ubp1 == offset_ub + 1); // falsified

  size_t idx;
  if(idx < size)
  {
    char *lb_idx = lb + idx;
    void *dummy_ub = ub;
    assert(lb <= lb_idx); // proved
    assert(lb_idx <= ub); // proved
  }

  // to produce a trace so that we can observe some intermittent values
  assert(size < max_malloc_size);
}
