int main()
{
  int *p = 0;

  for(int i = 0; i < 3; ++i)
  {
    {
      int x = 42;
      p = &x;
      *p = 1;
    }
  }

  return 0;
}
