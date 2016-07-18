
void func3()
{

}

void func2()
{
  func3();
}

void func1()
{
  func2();
}

int main()
{
  func1();
  return 0;
}
