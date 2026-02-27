// Expected failure: forall constraint too weak for assert.
#define N 4
typedef struct { int coeffs[N]; } poly;
int main() {
  poly a;
  __CPROVER_assume(__CPROVER_forall {
    unsigned k; k < N ==> a.coeffs[k] >= -200 && a.coeffs[k] <= 200
  });
  __CPROVER_assert(
    a.coeffs[0] >= -100 && a.coeffs[0] <= 100, "tight bound");
}
