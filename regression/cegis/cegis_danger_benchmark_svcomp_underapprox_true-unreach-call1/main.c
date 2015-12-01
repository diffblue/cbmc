int main(void) {
  unsigned int x = 0;
  unsigned int y = 1;

  while (x < 6) {
    x++;
    y *= 2;
  }

  __CPROVER_assert(y % 3, "A");
  return 0;
}
