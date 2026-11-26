extern "C" void __CPROVER_assert(bool, const char *);
struct sequence
{
  int log = 0;
  sequence &operator,(int k)
  {
    log = log * 10 + k;
    return *this;
  }
};
enum class flag
{
  a = 1,
  b = 2
};
int operator,(flag x, flag y)
{
  return static_cast<int>(x) * 10 + static_cast<int>(y);
}
struct plain
{
  int v;
};
int main()
{
  // [over.match.oper]/1: a user-declared operator, is selected for an operand
  // of class or enumeration type
  sequence s;
  s, 1, 2;
  __CPROVER_assert(s.log == 12, "member operator,");
  int r = (flag::b, flag::a);
  __CPROVER_assert(r == 21, "non-member operator, for enumerations");
  plain p{3};
  int q = (p, 4);
  __CPROVER_assert(q == 4 && p.v == 3, "built-in comma");
  int t = ((void)s, 5);
  __CPROVER_assert(t == 5 && s.log == 12, "void operand");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
