struct S
{
  auto get()
  {
    return 42;
  }
};

int main()
{
  S s;
  int r = s.get();
  __CPROVER_assert(r == 42, "auto member");
  return 0;
}
