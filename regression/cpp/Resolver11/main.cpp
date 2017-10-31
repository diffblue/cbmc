struct A
{
  bool func() { return false; }
  bool func() const { return true; }

  bool test()
  {
    return func();
  }

  bool test()const
  {
    return func();
  }
};

int main()
{
  A a;
  __CPROVER_assert(a.test() == false, "");
  const A a2;
  __CPROVER_assert(a2.test() == true, "");
}
