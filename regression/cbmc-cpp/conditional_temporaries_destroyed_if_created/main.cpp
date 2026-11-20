// N5008 [class.temporary]/4: a temporary is destroyed at the end of the
// full-expression that creates it, and only if it was created: one in a
// branch of ?:, or in the right operand of && or ||, exists only if that
// operand was evaluated ([expr.cond]/1, [expr.log.and]/1, [expr.log.or]/1).
extern "C" void __CPROVER_assert(bool, const char *);
// a nondeterministic choice in CBMC (no body); natively, an argument
bool nondet_bool();

int constructed = 0, destroyed = 0;

struct S
{
  int value;
  explicit S(int v) : value(v)
  {
    ++constructed;
  }
  S(const S &other) : value(other.value)
  {
    ++constructed;
  }
  ~S()
  {
    ++destroyed;
  }
  int get() const
  {
    return value;
  }
};

int test(bool b, bool c, bool d, bool e)
{
  constructed = destroyed = 0;
  int r = b ? 0 : S(1).get();
  __CPROVER_assert(constructed == destroyed, "one branch");
  __CPROVER_assert(constructed == (b ? 0 : 1), "created only if evaluated");

  constructed = destroyed = 0;
  int s = c ? S(2).get() : S(3).get();
  __CPROVER_assert(constructed == 1 && destroyed == 1, "both branches");
  __CPROVER_assert(s == (c ? 2 : 3), "selected branch");

  constructed = destroyed = 0;
  bool t = (d && S(4).get() == 4) || (e && S(5).get() == 5);
  __CPROVER_assert(constructed == destroyed, "logical operators");
  __CPROVER_assert(
    constructed == (d ? 1 : 0) + (!d && e ? 1 : 0) + (d && e ? 0 : 0),
    "created only if evaluated, && and ||");
  return r + s + t;
}

#ifdef __CPROVER__
int main()
{
  test(nondet_bool(), nondet_bool(), nondet_bool(), nondet_bool());
  __CPROVER_assert(constructed == 0, "WRONG (must FAIL)");
  return 0;
}
#else
int main()
{
  for(int i = 0; i < 16; ++i)
    test(i & 1, i & 2, i & 4, i & 8);
  // the last combination evaluates S(4)
  __CPROVER_assert(constructed == 0, "WRONG (must FAIL)");
  return 0;
}
#endif
