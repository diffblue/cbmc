// N5008 [temp.param]/7, [temp.arg.nontype]/1, [expr.const]/5: class-type
// non-type template arguments from constexpr constructors.
extern "C" void __CPROVER_assert(bool, const char *);

struct Fixed
{
  int value;
  int twice;
  constexpr Fixed(int v) : value(v), twice(2 * v)
  {
  }
};

struct Ordered
{
  int lo;
  int hi;
  constexpr Ordered(int x, int y) : lo(x), hi(y)
  {
    if(lo > hi)
    {
      int t = lo;
      lo = hi;
      hi = t;
    }
  }
};

template <Fixed F>
constexpr int sum()
{
  return F.value + F.twice;
}

template <Fixed F>
struct S
{
  static constexpr int v = F.value;
};

template <Ordered o>
constexpr int low()
{
  return o.lo;
}

int main()
{
  __CPROVER_assert(sum<Fixed(42)>() == 126, "parenthesised");
  __CPROVER_assert(sum<Fixed{7}>() == 21, "braced");
  __CPROVER_assert(S<Fixed(3)>::v == 3, "class template");
  __CPROVER_assert(low<Ordered(5, 2)>() == 2, "constructor body ran");
  static_assert(low<Ordered(9, 4)>() == 4, "constant expression");
  static_assert(sum<Fixed(1)>() == 3, "constant expression 2");
  __CPROVER_assert(sum<Fixed(1)>() == 4, "WRONG (must FAIL)");
  return 0;
}
