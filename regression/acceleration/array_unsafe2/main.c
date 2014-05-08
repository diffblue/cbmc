int main(void) {
  int A[10];
  int B[10];
  int i;
  int tmp;

  for (i = 0; i < 10 && tmp != 0; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  assert(A[5] != B[5]);
}
