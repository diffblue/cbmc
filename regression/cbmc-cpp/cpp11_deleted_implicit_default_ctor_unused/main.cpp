// A class whose implicitly-declared default constructor is DELETED
// (a member without a default constructor, [class.default.ctor]/2)
// may be derived from and left UNUSED: the deleted definition is an
// error only when odr-used ([class.default.ctor]/4, [dcl.fct.def.delete]/2).
// CBMC eagerly generates the implicit definitions and errors on them.
// Reduced by cvise from a 99k-line goto-symex dog-food carrier
// (state.h: goto_statet's guard_exprt member).
extern "C" void __CPROVER_assert(bool, const char *);
struct symbol_exprt
{
  symbol_exprt(int);
};
struct ssa_exprt : symbol_exprt
{
};
struct guard_exprt
{
  guard_exprt(int);
};
struct goto_statet
{
  guard_exprt guard;
};
struct final : goto_statet
{
};
int main()
{
  __CPROVER_assert(true, "unused deleted implicit ctors are not an error");
  return 0;
}
