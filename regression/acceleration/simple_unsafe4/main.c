int main(void) {
  unsigned int x = 0x0ffffff1;

  while (x > 0) {
    x -= 2;
  }

  assert(!(x % 2));
}
