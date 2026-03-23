struct x
{
  void f();

  static int i;
};

void x::f()
{
}

int x::i = 42;

int main()
{
  void (x::*pf)() = &x::f;
  __CPROVER_assert(pf != 0, "pointer to member function is non-null");

  int *pi = &x::i;
  __CPROVER_assert(pi != 0, "pointer to static member is non-null");
}
