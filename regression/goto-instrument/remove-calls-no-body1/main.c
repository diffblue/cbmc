void func1();

void func3()
{
}

void func4()
{
  func1();
  func2();
}

void main()
{
  func1();
  func2();
  func3();
  func4();
}
