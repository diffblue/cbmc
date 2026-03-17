struct S
{
  S() = default;
  int x;
};

S make()
{
  return S();
}

int main()
{
  S s = make();
  return 0;
}
