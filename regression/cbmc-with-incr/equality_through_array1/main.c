void main ()
{
  int a[4];

  a[0] = 0;
  a[1] = 1;
  a[2] = 2;
  a[3] = 3;

  int x;
  int y;

  __CPROVER_assume(0 <= x && x < 4);
  __CPROVER_assume(0 <= y && y < 4);
  __CPROVER_assume(x + y < 4);

  assert(a[x] + a[y] == x + y);

  return 1;
}
