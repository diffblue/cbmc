
int x;

void func3()
{
  x = 6;
}

void func2()
{
  x = 3;
}

void func1()
{
  x = 1;
  func2();
  x = 2;
}

int main()
{
  x = 4;
  __CPROVER_ASYNC_0:
    func1();
  x = 5;

  return 0;
}

