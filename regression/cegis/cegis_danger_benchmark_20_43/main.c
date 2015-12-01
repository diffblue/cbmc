int main(void) {

  unsigned int x;


  while (x < 10) {
    x++;
  }

  __CPROVER_assert(x == 10, "A");

  return 0;
}
