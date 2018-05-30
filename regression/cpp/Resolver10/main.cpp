struct A
{
  int i;
  A():i(0){}
};

struct B: A
{
  void test()
  {
    i = 1;
    A();
    __CPROVER_assert(i==1, "");
  }
};

int main()
{
  B b;
  b.test();
}
