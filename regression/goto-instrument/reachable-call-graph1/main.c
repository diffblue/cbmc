
int x;

void func0()
{
  func0();
}

void func1()
{
  x = 1;
}

void func2()
{
  x = 2;
  func3();
}

void func3()
{
  x = 3;
}

void func4(int b)
{
  x = 4;
  if(b)
  {
    func5(0);
  }
}

void func5(int b)
{
  x = 5;
  func4(b);
}

void func6()
{
  x = 6;
}

void func7(int b)
{
  x = 7;
  if(b)
  {
    func8(0);
  }
}

void func8(int b)
{
  x = 8;
  func7(b);
}

void func9()
{
  x = 9;
  funca();
}

void funca()
{
  x = 10;
  func9();
}



int main()
{
  func1();
  func2();
  func4(1);

  return 0;
}
