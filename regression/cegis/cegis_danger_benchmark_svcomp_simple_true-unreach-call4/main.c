int main(void) {
  unsigned int x = 0x0ffffff0;

  while (x > 0) {
    x -= 2;
  }

  __CPROVER_assert(!(x % 2), "A");

  return 0;
}
