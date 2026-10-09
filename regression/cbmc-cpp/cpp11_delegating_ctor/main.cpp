// C++11 delegating constructor
struct S
{
  int x;
  S(int v) : x(v)
  {
  }
  S() : S(42)
  {
  }
};
int main()
{
  S s;
  __CPROVER_assert(s.x == 42, "delegating ctor");
  return 0;
}
