int main()
{
  int *p, *q, *a, *b;

  q = a;
  p = b;

  *p = 1;
  *q = 2;

  // this should work if no pointer checks are enabled
  assert(*p == 1);
  assert(*q == 2);
}
