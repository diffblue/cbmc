
void func2()
{

}

void func1()
{
  func2();
}

int main()
{
  func1();
  func1();

  return 0;
}

