int d=0;

void f1()
{
  d=1;
}

int main()
{
  int x=2;
  int y=3;

  f1();

  if(x && y && d)
    return 0;
}

