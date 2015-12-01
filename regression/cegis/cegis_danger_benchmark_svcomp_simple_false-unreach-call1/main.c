int main(void) {
  unsigned int x = 0;

  while (x < 0x0fffffff) {
    x += 2;
  }

  __CPROVER_assert(x % 2, "A");
  return 0;
}
