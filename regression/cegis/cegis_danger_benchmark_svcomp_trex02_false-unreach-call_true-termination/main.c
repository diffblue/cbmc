int main(void) {
  int x;

  while (x > 0) {
    int c;
    if(c) x--;
    else x--;
  }

  __CPROVER_assert(x==0, "A");

  return 0;
}
