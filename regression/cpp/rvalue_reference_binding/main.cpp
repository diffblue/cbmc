// Test that rvalue references can bind to temporaries and that
// functions with rvalue reference parameters can be called.

struct A
{
  int x;
};

A make_a()
{
  A a;
  a.x = 42;
  return a;
}

void take_rvalue(A &&a)
{
}

void take_rvalue_default(A &&a = A())
{
}

int main()
{
  take_rvalue(make_a());
  take_rvalue(A());
  take_rvalue_default();
  return 0;
}
