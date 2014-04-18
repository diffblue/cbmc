int main(void) {
  unsigned int x = 0;

  while (x < 0x0fffffff) {
    if (x < 0xfff1) {
      x++;
    } else {
      x += 2;
    }
  }

  assert(!(x % 2));
}
