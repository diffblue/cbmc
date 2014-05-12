#define N 10

int main(void) {
  int A[N];
  int i;

  for (i = 0; A[i] != 0; i++) {
    if (i >= N) {
      break;
    }
  }

  assert(i <= N);
}
