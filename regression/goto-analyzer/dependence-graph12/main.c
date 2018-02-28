int a;

void func()
{
}

void main(void)
{
  if(a < 7)
  {
    goto L;
  }

  if(a < 10)
  {
    func();
  L:
    a = 1;
    a = 2;
  }
}
