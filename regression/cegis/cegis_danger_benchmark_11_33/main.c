int main(void) {
  int x;

  if (x < 100 || x > 200) {
    return 0;
  }

  x=x;

  while (x > 0) {
    x -= 2;
  }

  __CPROVER_assert(x >= 0, "A");
  return 0;
}
