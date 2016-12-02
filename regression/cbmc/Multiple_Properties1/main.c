int main () {
  int x, y;
  __CPROVER_assume(x>=100 && y<=1000 & x>y+2);
  x--;
  assert(x>y);
  x--;
  assert(x>y);
  x--;
  assert(x>y);
  y=0;
  assert(x>y);

  return 0;
}
