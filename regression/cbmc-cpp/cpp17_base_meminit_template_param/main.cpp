extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [class.base.init]/2: a mem-initializer-id may designate the
// base class by any name denoting that type -- including the template
// PARAMETER the base is named by (`renamedt(underlyingt v) :
// underlyingt(v)`).  CBMC used to convert this but silently DROP the
// initialization (any explicit POD-base mem-initializer, in fact --
// even plain-named ones): the base subobject stayed nondeterministic.
// Fixed 2026-07-21 ([class.base.init]/7 slicing assignment).
// The shape of goto-symex/renamed.h, part of what blocks the
// goto_symex_state.h dog-food group.
// g++/clang++ accept and verify at runtime.

struct payloadt
{
  int x;
};

template <typename underlyingt>
struct renamedt : underlyingt
{
  // N5008 [class.base.init]/2: the mem-initializer-id may name the
  // base class via the template parameter
  explicit renamedt(underlyingt value) : underlyingt(value)
  {
  }
};

int main()
{
  payloadt p;
  p.x = 5;
  renamedt<payloadt> r(p);
  __CPROVER_assert(r.x == 5, "base mem-init via template parameter");
  return 0;
}
