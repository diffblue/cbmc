#include <assert.h>
#include <stdint.h>

typedef struct
{
  int32_t coeffs[256];
} poly;

typedef struct
{
  poly vec[8];
} polyvec;

int main()
{
  union
  {
    polyvec y;
    polyvec h;
  } yh;

  unsigned k;
  __CPROVER_assume(k < 256);

  polyvec nondet_val;
  yh.y = nondet_val;

  __CPROVER_assume(yh.y.vec[0].coeffs[k] > -100 && yh.y.vec[0].coeffs[k] < 100);

  assert(yh.h.vec[0].coeffs[k] > -100 && yh.h.vec[0].coeffs[k] < 100);
}
