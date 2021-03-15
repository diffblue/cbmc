struct A
{
  int i;
};

struct B: public A
{
  int j;
  B():j(0) { }
};

int main()
{
  B b1;
  b1.i=10;
  b1.j=20;

  B b2(b1);

  assert(b2.i == 10);
  assert(b2.j == 20);
}
