int main(void) {
  unsigned int x;

  while (x < 0x0fffffff) {
    x++;
  }

  __CPROVER_assert(x >= 0x0fffffff, "A");
  return 0;
}
