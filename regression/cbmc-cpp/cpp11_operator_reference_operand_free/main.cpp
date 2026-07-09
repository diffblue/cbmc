// N5008 [over.match.oper]/3.3 + [basic.lookup.argdep]/2: for `a @ b`, the set of
// non-member candidates is the unqualified lookup of operator@ in the context of
// the expression, EXCEPT THAT ALL MEMBER FUNCTIONS ARE IGNORED, together with
// the operators found by argument-dependent lookup on the operands.
//
// Here the operator expression `static_cast<basic_ostream<char> &>(base) << "hi"`
// appears inside mstreamt's own member operator<< template.  Ordinary
// unqualified lookup of operator<< finds that enclosing member (which is not
// viable for a basic_ostream left operand) and would hide the free
// operator<<(basic_ostream<C> &, const char *).  Two rules make the free
// operator selectable:
//   * member functions are excluded from the non-member candidate set, and
//   * ADL on the reference-typed left operand strips the reference to reach
//     basic_ostream<char>, whose associated namespace holds the free template
//     operator<< ([basic.lookup.argdep]/2: a reference argument's associated
//     types are those of the referenced type).
// The free operator (a function template) is then deduced and selected instead
// of falling back to the built-in shift.  This is the `const char *` half of
// the residual src/util parse_options.cpp / typecheck.cpp dog-food shl noise.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

template <class C>
struct basic_ostream
{
  int tag = 0;
};

// Free (non-member) function-template operator<<; hidden from ordinary lookup
// inside mstreamt::operator<< by the enclosing member, reachable only via ADL.
template <class C>
basic_ostream<C> &operator<<(basic_ostream<C> &os, const char *)
{
  os.tag = 9;
  return os;
}

struct mstream
{
  basic_ostream<char> base;
  template <class T>
  mstream &operator<<(const T &x)
  {
    static_cast<basic_ostream<char> &>(base) << x;
    return *this;
  }
  int tag() const
  {
    return base.tag;
  }
};

int main()
{
  mstream ms;
  ms << "hi";
  __CPROVER_assert(
    ms.tag() == 9,
    "free template operator<< selected via reference operand and ADL");
  __CPROVER_assert(ms.tag() != 9, "WRONG must FAIL");
  return 0;
}
