// Signed variable bounds.
#define N 4
int arr[N];
int main() {
  __CPROVER_assume(__CPROVER_forall {
    int k; (k >= 0 && k < N) ==> arr[k] >= 0
  });
  __CPROVER_assert(arr[1] >= 0, "signed bound");
}
