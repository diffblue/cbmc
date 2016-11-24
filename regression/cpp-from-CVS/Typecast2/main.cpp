struct myA
{
  int i;
};

struct myB: myA
{
  int j;
};

int main()
{
  myA a;
  myB b;

  b.j = 11;
  *(myA *)(&b) = a;

  assert(b.j == 11);
  assert(b.i == a.i);
}
