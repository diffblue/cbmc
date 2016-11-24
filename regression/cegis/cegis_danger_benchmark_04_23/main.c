int main(void) {
  unsigned int x;
  unsigned int len;
  unsigned int i;

  len = x * 4;
  i = 0;

  while (i * 4 < len && i < x) {
    i++;
  }

  __CPROVER_assert(i * 4 < len || i >= x, "A");
  return 0;
}
