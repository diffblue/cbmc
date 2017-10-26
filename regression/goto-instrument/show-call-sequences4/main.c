void foo()
{
  moo();
  boo();
}

void moo()
{
  return; 
}

void boo()
{
  return;
}

int main()
{
  moo();
  foo();
  return 0;
}