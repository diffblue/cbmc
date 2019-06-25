void stub(int *x);

void main()
{
  int x;
  void (*foo)(int *);
  foo = &stub;
  foo(&x);
  assert(x == 5);
}
