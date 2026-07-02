// N5008 [over.match.ctor]/1 with [namespace.udecl]/3: the candidate functions
// for initializing a class object are the constructors of that class.  A base
// class's constructors are NOT constructors of the derived class unless
// explicitly inherited with a using-declaration.  In particular the base's
// (copy) constructor must not make the derived class constructible from an
// unrelated sibling that merely shares the same base.
//
// This mirrors CBMC's own irept hierarchy: `exprt` and `source_locationt` both
// derive from `irept`.  When resolving the mem-initializer
//   code_assumet(exprt expr) : codet(ID_assume, {std::move(expr)})
// the two candidates are codet(irep_idt, source_locationt) and
// codet(irep_idt, operandst).  The braced argument {expr} is a single exprt, so
// only the operandst (std::vector<exprt>) overload is viable; source_locationt
// is not constructible from an exprt.  CBMC used to treat source_locationt as
// viable because it had merged irept's copy constructor irept(const irept&)
// into source_locationt's constructor set as an inherited (from_base)
// component, and exprt -> const irept& is a derived-to-base binding.  That made
// the constructor call ambiguous ("symbol 'codet' does not uniquely resolve").
//
// Here `exprt_m` and `loc_m` are the two siblings under `treet`; the braced
// argument {e} (an exprt_m) must select code_m(int, exprt_m), never the
// base-inherited path to code_m(int, loc_m).  g++ and clang++ accept this and
// select the exprt_m overload.
//
// Non-vacuous: assertion.2 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct treet
{
  int data;
  treet()
  {
  }
  // A user-declared copy constructor is materialised as a constructor
  // component of `treet` and merged into `loc_m` as an inherited (from_base)
  // component -- exactly as irept's constructors are merged into
  // source_locationt.  With a trivial base this leak does not occur.
  treet(const treet &)
  {
  }
};

struct exprt_m : treet
{
};

struct loc_m : treet
{
  loc_m()
  {
  }
};

int g = 0;

struct code_m
{
  code_m(int, loc_m)
  {
    g = 1;
  }
  code_m(int, exprt_m)
  {
    g = 2;
  }
};

int main()
{
  exprt_m e;
  e.data = 3;
  code_m c(0, {e});
  __CPROVER_assert(
    g == 2, "braced sibling arg does not match base-inherited ctor");
  __CPROVER_assert(g != 2, "WRONG must FAIL");
  return 0;
}
