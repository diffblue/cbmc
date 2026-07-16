// N5008 [class.base.init]/6: a mem-initializer naming the constructor's
// own class makes it a DELEGATING constructor; the target constructor
// is selected by overload resolution and no other member initialization
// takes place.
//
// KNOWNBUG: recognition of the delegation is DECLARATION-ORDER
// dependent.  When the delegating constructor is declared BEFORE its
// target, the front end fails to recognize the delegation (the class's
// constructor components are not yet visible to the detector in
// full_member_initialization) and falls back to default-initializing
// the members:
//  * if a member has no default constructor, conversion fails hard with
//    "found no match" for a zero-argument constructor call -- this is
//    how dog-fooding src/goto-programs/goto_program.cpp surfaced it:
//    goto_programt::instructiont's default constructor delegates and is
//    declared before its target, and member _code (goto_instruction_codet)
//    has no default constructor;
//  * otherwise members are silently default-initialized and the
//    delegation's effect is lost (wrong values, no diagnostic).
//
// This test captures both flavors: member `c` has no default
// constructor (hard error today), and the assertions catch the silent
// wrong-value flavor should conversion start succeeding.  Declaring the
// delegating constructor AFTER the target makes both work today.
//
// g++/clang++ verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct payloadt
{
  int v;
  explicit payloadt(int x) : v(x)
  {
  }
};

struct S
{
  payloadt c;
  int t;
  S() : S(7) // delegating; declared BEFORE its target
  {
  }
  explicit S(int type) : c(payloadt(type)), t(type)
  {
  }
};

int main()
{
  S i;
  __CPROVER_assert(i.c.v == 7, "member initialized via delegation");
  __CPROVER_assert(i.t == 7, "scalar initialized via delegation");
  return 0;
}
