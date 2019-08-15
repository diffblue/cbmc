void f(int y)
{
  if(y == 5)
  {
    for(int i = 0; i < 20; ++i)
    {
    }
    y = 10;
  }
}

int main(int argc, char **argv)
{
  f(argc);
  assert(argc == 1);
}
