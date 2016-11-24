int main(void) {
  unsigned int x, y;

  x = 0;
  y = 1;

  while (x < 1000003) {
    unsigned int nondet_0;
    if (nondet_0) {
      x++;
    }

    unsigned int nondet_1;
    if (nondet_1) {
      y++;
    }
  }

  __CPROVER_assert(x == y, "A");
  return 0;
}
