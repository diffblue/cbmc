int func1(int arg1, int arg2);

void func3()
{
}

void func4()
{
  func1(567, 285);
  func2();
}

void main()
{
  int ret1;

  ret1 = func1(567, 285);
  func2();
  func3();
  func4();
}
