// N5008 [class.base.init]/9 + [class.default.ctor]/4: when a base class
// subobject is initialized by the (implicitly defined) default
// constructor of the derived class, the base's own default constructor
// runs, and per [class.base.init]/9.1 a member with a default member
// initializer (NSDMI, [class.mem.general]/10) is initialized from it.
//
// KNOWNBUG: the implicit default construction of a DERIVED class object
// drops the base's NSDMIs -- `opt o;` below leaves o.e / o.p.x nondet.
// Boundary (probed):
//  * a direct object of the base itself gets the NSDMI correctly;
//  * spelling an explicitly-defaulted constructor (`B() = default;`) in
//    the base ALSO makes it work -- only the fully implicit constructor
//    of a base under derivation loses the initializer;
//  * one derivation level with a direct bool member suffices (the
//    nesting and class template of the original are unnecessary).
//
// Found by reducing (cvise on cbmc-preprocessed source, then by hand)
// the std::optional<std::string> residual: _Optional_payload_base's
// `bool _M_engaged = false;` was lost, so a default-constructed optional
// had nondet has_value().  g++/clang++ verify at runtime.  Flip to CORE
// when implicit default constructors of bases apply NSDMIs.
extern "C" void __CPROVER_assert(bool, const char *);

struct B
{
  bool e = false;
};
struct D : B
{
};

struct PB
{
  int x = 42;
};
struct M
{
  PB p;
};
struct N : M
{
};

int main()
{
  D d;
  __CPROVER_assert(!d.e, "base bool NSDMI applied");
  N n;
  __CPROVER_assert(n.p.x == 42, "nested int NSDMI applied");
  return 0;
}
