void f(int y)
{
  if(y == 5)
  {
    __CPROVER_assume(0);
    y = 10;
  }
}

int main(int argc, char **argv)
{
  f(argc);
  assert(argc == 1);
}
