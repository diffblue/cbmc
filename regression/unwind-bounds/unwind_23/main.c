
void func()
{
  int i;
  for(i = 0; i < 10; i++)
  {
    if (i == 7)
      return;
  }
  i = 12;
}

int main()
{
  func();
}

