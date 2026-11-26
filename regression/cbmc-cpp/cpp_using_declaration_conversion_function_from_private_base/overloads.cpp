extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  operator int() const
  {
    return 1;
  }
  operator char() const
  {
    return 2;
  }
};
// [class.access.general]/5: access is checked after overload resolution;
// the private B::operator char is a candidate, but operator int (an exact
// match, made public by the using-declaration) is selected
struct A : private B
{
  using B::operator int;
};
int main()
{
  A a;
  int x = a;
  char c = (char)(int)a;
  __CPROVER_assert(x == 1 && c == 1, "accessible conversion selected");
  __CPROVER_assert(x != 1, "WRONG (must FAIL)");
}
