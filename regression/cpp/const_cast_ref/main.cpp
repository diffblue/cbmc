struct S
{
  int x;
};

void f(const S &s)
{
  S &m = const_cast<S &>(s);
  m.x = 42;
}

int main()
{
  S s{0};
  f(s);
  __CPROVER_assert(s.x == 42, "ok");
  return 0;
}
