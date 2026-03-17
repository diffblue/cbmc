struct S
{
  int x;
  S() : x(42)
  {
  }
  S(int) : S()
  {
  }
};

int main()
{
  S s(0);
  return s.x;
}
