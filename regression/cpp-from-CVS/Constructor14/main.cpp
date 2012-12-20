struct A
{
  A(int i):i(i){}
  int i;
};

A a(1);


A b = 1;

int main()
{
  A c(1);
  A d=1;
  assert(a.i == 1);
  assert(b.i == 1);
  assert(c.i == 1);
  assert(c.i == 1);
}
