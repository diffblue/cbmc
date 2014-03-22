int main(void) {
  int i;
  int x = 0;

  for (i = 0; i < 100; i++) {
    if (i % 7) {
      if (i % 2) {
        x += i;
      } else if (i % 3) {
        x -= i;
      } else {
        x += 2*i;
      }

      x++;
    } else {
      x--;
    }
  }

  assert(x < 100);
}
