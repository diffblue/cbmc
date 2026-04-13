#include <stdint.h>

#define __contract__(x) x
#define requires(...) __CPROVER_requires(__VA_ARGS__)
#define ensures(...) __CPROVER_ensures(__VA_ARGS__)
#define assigns(...) __CPROVER_assigns(__VA_ARGS__)

/* clang-format off */
#define array_bound(arr, n, lo, hi, qvar)              \
  __CPROVER_forall {                                   \
    unsigned qvar; ((qvar) >= (n)) || ((arr)[(qvar)] >= (int)(lo) && (arr)[(qvar)] < (int)(hi)) \
  }
/* clang-format on */

#define N 256
#define K 8

typedef struct
{
  int32_t coeffs[N];
} poly;
typedef struct
{
  poly vec[K];
} polyveck;

typedef union
{
  polyveck a;
  polyveck b;
} ab_t;

/* clang-format off */
void stub(polyveck *v)
__contract__(
  requires(__CPROVER_is_fresh(v, sizeof(polyveck)))
  assigns(__CPROVER_object_upto(v, sizeof(polyveck)))
  ensures(array_bound(v->vec[0].coeffs, N, 0, 100, _i0))
  ensures(array_bound(v->vec[1].coeffs, N, 0, 100, _i1))
);
/* clang-format on */

void harness(void)
{
  ab_t arr[1];
  ab_t *p = arr;
  stub(&p->a);
  stub(&p->b);
}

int main(void)
{
  harness();
}
