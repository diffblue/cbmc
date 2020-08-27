int main()
{
  int a;
  int temp = a;
  a = a + 1;
  assert(a == temp + 1);
  return 0;
}
