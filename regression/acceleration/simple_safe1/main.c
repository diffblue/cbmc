int main(void) {
  unsigned int x = 0;

  while (x < 100) {
    x += 2;
  }

  assert(!(x % 2));
}
