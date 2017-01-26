
void func() {}

int main()
{
  int i;
  int x;

  x = 0;

  for(i = 0; i < 10; i++) { // 10
    if(x)
      x = 0;
    else
      x = 1;
  }

  x = 1;

  for(i = 0; i < 10;) { // 10
    if(x)
      i++;
    else
      i++;
  }

  x = 2;

  for(i = 0; i < 17; i++) // 17
  {
    func();
  }
}

