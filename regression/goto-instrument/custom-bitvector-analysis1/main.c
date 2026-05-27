int main()
{
  int x = 0;
  int *p = &x;
  x = *p + 1;
  return x;
}
