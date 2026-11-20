void foo(void)
{
  for(int i = 0; i < 2; ++i)
    ;
}
int main()
{
  for(int i = 0; i < 2; ++i)
    for(int j = 0; j < 2; ++j)
      foo();
  return 0;
}
