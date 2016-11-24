int main(void) {
  unsigned int x = 0;
  //unsigned short N;
  unsigned int N;
  N %= 0xFFFF;

  while (x < N) {
    x += 2;
  }

  __CPROVER_assert(x % 2, "A");
  return 0;
}
