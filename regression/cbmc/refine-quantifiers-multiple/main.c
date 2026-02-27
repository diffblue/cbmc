// Multiple quantifiers over different arrays.
#define N 4
typedef struct { int a[N]; int b[N]; } pair;
int main() {
  pair p;
  __CPROVER_assume(__CPROVER_forall {
    unsigned k; k < N ==> p.a[k] >= 0 && p.a[k] <= 10
  });
  __CPROVER_assume(__CPROVER_forall {
    unsigned k; k < N ==> p.b[k] >= 0 && p.b[k] <= 10
  });
  __CPROVER_assert(p.a[2] + p.b[2] <= 20, "sum bound");
}
