// Test 1: Basic forall in assume, concrete index in assert.
// With lazy refinement, only 1 instance (index 3) is needed.

#define N 8

typedef struct
{
  int coeffs[N];
} poly;

int main()
{
  poly a;

  __CPROVER_assume(__CPROVER_forall {
    unsigned k;
    k < N ==> a.coeffs[k] >= -100 && a.coeffs[k] <= 100
  });

  __CPROVER_assert(a.coeffs[3] >= -100 && a.coeffs[3] <= 100, "bound");
}
