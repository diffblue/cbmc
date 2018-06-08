struct S
{
  S(int _x) : x(_x) {}
  int x;
};

S s(42);

int main()
{
  __CPROVER_assert(s.x == 42, "");
  return 0;
}
