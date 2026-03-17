int main()
{
  int x = 0;
  int *p = &x;
  if(p)
    x = *p + 1;
  return x;
}
