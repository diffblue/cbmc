// N5008 [over.call.func]/3, [basic.lookup.argdep]/1: the EXPLICIT call
// `operator==(o)` inside a member function uses ordinary unqualified
// lookup; finding the member makes it a member call (this->operator==)
// and suppresses ADL.  CBMC's [over.match.oper]/3.3 member-stripping --
// correct only for operator EXPRESSIONS' non-member candidate lookup --
// also fired here whenever ANY free operator== existed, leaving only
// non-viable free candidates: "found no match for symbol 'operator=='".
// Found dog-fooding src/goto-programs/loop_ids.cpp (loop_idt::operator!=).
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct other
{
  int v;
};

bool operator==(const other &a, const other &b)
{
  return a.v == b.v;
}

struct thing
{
  int id;
  bool operator==(const thing &o) const
  {
    return id == o.id;
  }
  bool operator!=(const thing &o) const
  {
    return !operator==(o);
  }
};

int main()
{
  thing a{1};
  thing b{2};
  __CPROVER_assert(a != b, "member operator== found by unqualified call");
  return 0;
}
