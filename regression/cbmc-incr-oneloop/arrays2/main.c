int main()
{
  int a[5], b[5];
  int x;
  for(unsigned i = 0; i < 5; i++)
  {
    a[i] = b[i];
    if(i == 3)
      b[i] = x;
    if(i > 0)
      assert(a[i - 1] == b[i - 1]);
  }
  assert(a[4] == b[4]);
}
