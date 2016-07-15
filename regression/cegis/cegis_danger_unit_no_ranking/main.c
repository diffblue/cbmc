int main(void) {
  int x;

  x = 1000003;

  while (x > 0) {
    x -= 2;
  }

  __CPROVER_assert(x >= 0, "A");
  return 0;
}
