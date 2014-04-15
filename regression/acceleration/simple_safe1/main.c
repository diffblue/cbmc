int main(void) {
  int x = 0;

  while (x < 100) {
    x += 2;
  }

  assert(!(x % 2));
}
