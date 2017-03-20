
int x;

void h()
{
  x = 1;
}

void g()
{
  h();
}

void f()
{
  g();
}

int main()
{
  f();
}

