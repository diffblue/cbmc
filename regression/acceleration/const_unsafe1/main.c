int main(void) {
  unsigned int x = 1;
  unsigned int y = 0;

  while (y < 10) {
    x = 0;
    y++;
  }

  assert(x == 1);
}
