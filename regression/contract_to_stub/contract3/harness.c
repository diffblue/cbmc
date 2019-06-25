void stub(int *x);

void main()
{
  int x = 1;
  stub(&x);
  assert(x == 5);
}
