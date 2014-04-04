int main(void) {
  int i = 0;

  while (i < 100) {
    if (i % 2) {
      i++;
    } else {
      i += 3;
    }
  }

  assert(i < 100);
}
