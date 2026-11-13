// N5008 [over.match.oper]/3.3, [over.built]/16, [over.ics.rank]/2.1: for
// `x == y' with both operands of the same enumeration type the built-in
// operator==(E, E) is an exact match, and a candidate that needs a
// user-defined conversion for an operand (the hidden friend below, found by
// argument-dependent lookup through the enumeration's class) is worse.  The
// shape of libstdc++ 16's text_encoding, whose friend operator== compares
// `__encoding.mib() == __i'.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
  enum class id : int
  {
    a = 1,
    b = 2
  };
  E(id i) : r(i)
  {
  }
  id mib() const
  {
    return r;
  }
  friend bool operator==(const E &e, id i)
  {
    return e.mib() == i;
  }
  id r;
};
int main()
{
  E e{E::id::b};
  __CPROVER_assert(
    e == E::id::b && !(e == E::id::a) && E::id::a != E::id::b,
    "built-in operators");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
