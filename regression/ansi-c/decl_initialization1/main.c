void foo()
{
}

int cr_register_hook()
{
  int y = ({ return 1; 1; });

  return y;
}

int main()
{
  foo();
  return cr_register_hook();
}
