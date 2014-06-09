int main(void) {
  unsigned int x = 0;
  unsigned int y = 0;

  while (x < 0x0fffffff) {
    y = 0;

    while (y < 10) {
      y++;
    }

    x++;
  }

  assert(x % 2);
}
