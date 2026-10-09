// N5008 [dcl.fct.def.default]/5 + [class.default.ctor]/2: an explicitly
// defaulted default constructor whose implicit definition would be
// ill-formed (base without a default constructor) is defined as
// DELETED; the program is only ill-formed when it is odr-used.
// Nothing here uses it.  Reduced by cvise (fleet cv107) from the
// 97k-line goto-symex dog-food carrier -- the `= default` is the delta
// from the already-fixed implicit-constructor sibling
// (cpp11_deleted_implicit_default_ctor_unused).
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
struct goto_symex_statet : goto_statet
{
  goto_symex_statet() = default;
};
int main()
{
  __CPROVER_assert(true, "unused deleted defaulted ctor is not an error");
  return 0;
}
