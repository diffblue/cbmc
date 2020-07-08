void test(int *x, int *y)
{
  assert(x);
  assert(y);
  assert(x == y);
  assert(x != y);
  assert(*x == *y);
}
