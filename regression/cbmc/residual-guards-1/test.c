void g()
{
  g();
}

void f(int y)
{
  if(y == 5)
  {
    g();
    y = 10;
  }
}

int main(int argc, char **argv)
{
  f(argc);
  assert(argc == 1);
}
