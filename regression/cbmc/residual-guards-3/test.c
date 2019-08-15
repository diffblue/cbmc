void g(int x)
{
  return g(x + 1);
}

void f(int y)
{
  if(y == 5)
  {
    g(1);
    y = 10;
  }
}

int main(int argc, char **argv)
{
  f(argc);
  assert(argc == 1);
}
