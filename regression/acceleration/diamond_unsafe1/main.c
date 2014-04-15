int main(void) {
  int x = 0;
  int y;

  while (x < 99) {
    if (y % 2 == 0) {
      x++;
    } else {
      x += 2;
    }
  }

  assert((x % 2) == (y % 2));
}
