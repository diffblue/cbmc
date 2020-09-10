#include "first_one.h"
#include <assert.h>

static int static_function(int a)
{
  assert(a == 0);
  return a;
}

int non_static_function(int a)
{
  return static_function(a);
}

static int with_matching_signature(int a)
{
  assert(0 && "this is not reachable as far as goto-harness is concerned");
  return 0;
}

void non_static_with_non_matching_signature(void)
{
  // this is just here so `static_with_matching_signature` has a non-file-local use
  assert(static_with_matching_signature(10) == 10);
}
