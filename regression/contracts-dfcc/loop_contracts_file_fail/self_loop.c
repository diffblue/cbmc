void foo(int j)
{
  for(unsigned i = 0; i < 8; i++)
  {
  }
  if(j)
  {
  loop:
    goto loop;
  }
}

int main()
{
  foo(0);
  return 0;
}
