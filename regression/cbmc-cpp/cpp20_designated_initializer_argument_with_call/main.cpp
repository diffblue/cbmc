// A designated-initializer-list argument whose clause initializes from a
// call with a prvalue argument for an rvalue reference parameter
// (`.tag = reg(s + "x")' with std::string's operator+(string &&, ...)).
// The clause's initializer was type-checked twice, and the second time the
// argument of operator+ was an lvalue: "invalid implicit conversion from
// 'struct str &' to 'struct str &&'".
extern "C" void __CPROVER_assert(bool, const char *);
struct str
{
  int n;
  str(int k) : n(k)
  {
  }
  str(const str &o) : n(o.n)
  {
  }
};
str operator+(str &&a, int b)
{
  return str(a.n + b);
}
static int reg(const str &s)
{
  return s.n;
}
struct rec
{
  unsigned idx;
  int tag;
};
struct sink
{
  rec r;
  int which = 0;
  void push_back(const rec &x)
  {
    r = x;
    which = 1;
  }
  void push_back(rec &&x)
  {
    r = x;
    which = 2;
  }
};
int main()
{
  sink v;
  v.push_back({.idx = 1, .tag = reg(str(2) + 3)});
  __CPROVER_assert(v.r.idx == 1 && v.r.tag == 5, "pushed");
  __CPROVER_assert(v.which == 2, "rvalue overload");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
