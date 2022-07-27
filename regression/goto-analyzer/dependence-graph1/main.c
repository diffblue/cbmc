
int x;

void func()
{
  int r;

  r = x;
}

int main()
{
  x = 1;
  func();

  return 0;
}

