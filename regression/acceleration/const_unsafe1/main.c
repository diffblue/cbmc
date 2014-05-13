int main(void) {
  unsigned int x;

  while (nondet()) {
    x = 0;
  }

  assert(x == 1);
}
