typedef void (ft)();

void foo()
{
}

void zz(ft f1, ft *f2)
{
  assert(f1==foo);
  assert(f2==foo);
}

int main()
{
  // gcc eats this
  zz(foo, foo);
}
