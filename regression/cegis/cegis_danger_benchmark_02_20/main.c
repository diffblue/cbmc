int main(void) {
  unsigned int x;
  unsigned int y;

  x = 0;
  y = 0;

  while (x < 1000003) {
    x++;

    int nondet_0;
    if (nondet_0) {
      y++;
    }
  }

  __CPROVER_assert(x != y, "A");
  return 0;
}
