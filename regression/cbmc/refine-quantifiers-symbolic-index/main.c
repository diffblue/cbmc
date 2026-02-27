// Forall in assume with symbolic index in assert.
#define N 8
typedef struct { int coeffs[N]; } poly;
int main() {
  poly a;
  unsigned i;
  __CPROVER_assume(__CPROVER_forall {
    unsigned k; k < N ==> a.coeffs[k] >= -100 && a.coeffs[k] <= 100
  });
  __CPROVER_assume(i < N);
  __CPROVER_assert(a.coeffs[i] >= -100 && a.coeffs[i] <= 100, "bound");
}
