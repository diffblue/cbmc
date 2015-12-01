int main(void) {
  unsigned int x = 1;
  unsigned int y;

  while (y > 0 && x < y) {
    if (x > 0 && x < y / x) {
      x *= x;
    } else {
      x++;
    }
  }

  __CPROVER_assert(y == 0 || x != y, "A");
  return 0;
}
