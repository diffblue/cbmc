
int x;

void i()
{

}

void h()
{
  x = 7;
  x = 8;
  x = 9;
  i();
  //i();
}

void g()
{

}

void f()
{
  g();
  h();
  x = 1;
}

int main()
{
  f();
  x = 2;
}

