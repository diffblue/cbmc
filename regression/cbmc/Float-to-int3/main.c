#include <assert.h>
#include <stdint.h>

int64_t nondet_int64_t();
double nondet_double();

int main(void)
{
  int64_t i = nondet_int64_t();

  __CPROVER_assume((i & (int64_t)0x7FF) == (int64_t)0);
  
  double di = (double)i;
  int64_t j = (int64_t)di;

  assert(i == j);

  return 0;
}

