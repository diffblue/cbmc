int main(void) {
  unsigned int x;
  unsigned int y = x;

  while (x < 1024) {
    x++;
    y++;
  }

  __CPROVER_assert(x == y, "A");
  return 0;
}
