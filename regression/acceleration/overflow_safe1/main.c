int main(void) {
  unsigned int x = 10;

  while (x >= 10) {
    x += 2;
  }

  assert(!(x % 2));
}
