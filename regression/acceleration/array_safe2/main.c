int main(void) {
  int A[2048];
  int B[2048];
  int i;
  int tmp;

  for (i = 0; i < 1024 && A[i] != 0; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  assert(A[1023] == B[1023]);
}
