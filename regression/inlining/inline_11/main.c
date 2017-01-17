
int x;

void g()
{
  x = 3;
}

void f()
{
  g();
  x = 1;
}

int main()
{
  f();
  x = 2;
}

