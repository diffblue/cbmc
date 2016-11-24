struct A
{
  int i;
};

int main()
{
  const A a;
  // not allowed
  a.i = 99;
}
