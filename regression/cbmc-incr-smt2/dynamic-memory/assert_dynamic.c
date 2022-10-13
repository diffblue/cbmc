#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

bool nondet_bool();

void main()
{
  char local;
  void *pointer = &local;
  const bool make_dynamic = nondet_bool();
  if(make_dynamic)
  {
    pointer = malloc(1);
  }
  assert(__CPROVER_DYNAMIC_OBJECT(pointer));
}
