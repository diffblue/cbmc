// N5008 [dcl.constexpr]/6, [expr.const]/9: a constexpr object of class type
// is usable in constant expressions, also through its constexpr member
// functions.  `constexpr W w{2}' initializes the unsigned long member from
// the int 2 ([dcl.init.aggr]/4.3, [conv.integral]).
extern "C" void __CPROVER_assert(bool, const char *);

struct W
{
  unsigned long n;
  const char *p;
  constexpr unsigned long size() const
  {
    return n;
  }
};

constexpr W global{3, "abc"};

int main()
{
  constexpr W w{2, "ab"};
  static_assert(w.size() == 2, "block scope");
  static_assert(global.size() == 3, "namespace scope");
  static_assert(w.n == 2, "member");
  __CPROVER_assert(w.size() + global.size() == 5, "run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
