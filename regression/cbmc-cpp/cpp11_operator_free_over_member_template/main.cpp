// N5008 [over.match.oper]/3, [over.match.best]/2: for `a << b`, the member and
// non-member operator<< candidates form a single overload set, and a
// non-template candidate is preferred over a function-template specialization
// when their conversion sequences are otherwise indistinguishable.  Moreover
// only the selected, odr-used specialization's body is instantiated
// ([temp.inst]/2, [basic.def.odr]) -- forming a candidate must not instantiate
// a member template's body.
//
// Regression test reduced from the src/util/message.h dog-food noise: mstreamt
// has a member `template <class T> operator<<(const T&)` whose body streams `x`
// to a std::ostream, plus a free `operator<<(mstreamt&, eomt)` for the `eom`
// manipulator.  `m << eom` must pick the free non-template operator; CBMC
// instead resolved (and instantiated the body of) the member template for
// T=eomt, whose `ostream << eomt` then failed with "operator 'shl' not
// defined".  Here the member template body is likewise ill-formed for eomt
// (ostream << eomt), so if it were (wrongly) selected/instantiated the program
// would not compile; picking the free operator both compiles and yields v==7.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct ostream
{
};
struct eomt
{
};

struct mstream
{
  int v = 0;
  template <class T>
  mstream &operator<<(const T &x)
  {
    ostream o;
    o << x; // ill-formed for T=eomt; only instantiated if this member is chosen
    v = 100;
    return *this;
  }
};

// free non-template operator for the manipulator type
mstream &operator<<(mstream &m, eomt)
{
  m.v = 7;
  return m;
}

int main()
{
  mstream ms;
  eomt e;
  ms << e; // must select the free non-template operator<<(mstream&, eomt)
  __CPROVER_assert(
    ms.v == 7,
    "free non-template operator<< chosen; member template not instantiated");
  __CPROVER_assert(ms.v != 7, "WRONG must FAIL");
  return 0;
}
