int main(void) {
  unsigned int i, c, a;

  i = 0;
  c = 0;

  while (i < 1000003) {
    c = c+i;
    i++;

  }

  __CPROVER_assert(a > 0, "A");
  return 0;
}
