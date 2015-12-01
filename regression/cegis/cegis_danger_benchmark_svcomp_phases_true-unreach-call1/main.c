int main(void) {
  unsigned int x = 0;

  while (x < 0x0fffffff) {
    if (x < 0xfff0) {
      x++;
    } else {
      x += 2;
    }
  }

  __CPROVER_assert(!(x % 2), "A");
  return 0;
}
