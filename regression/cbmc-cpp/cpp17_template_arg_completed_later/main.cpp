// A class template instantiated with a then-INCOMPLETE argument type
// in a declaration-only context ([temp.inst]/1 requires no
// instantiation there), where the argument type is COMPLETED later
// and the specialization is then genuinely used.  The later use is a
// new point of instantiation with the complete type ([temp.point]),
// so g++ and clang++ accept and the program verifies at runtime.
// CBMC caches the instance created at the declaration (with the
// incomplete base layout) and serves the stale instance to the later
// use: CONVERSION ERROR here; the variant whose constructor has a
// base mem-initializer (renamedt shape) reaches symbolic execution
// and fails an invariant in symex_assign.  Companion to the FIXED
// cpp17_incomplete_template_arg_decl (declaration-only case).
extern "C" void __CPROVER_assert(bool, const char *);

class ssa_exprt;

template <typename T>
struct renamedt : T
{
};

renamedt<ssa_exprt> f(const ssa_exprt &);

class ssa_exprt
{
public:
  int level;
};

renamedt<ssa_exprt> f(const ssa_exprt &e)
{
  renamedt<ssa_exprt> r;
  r.level = e.level;
  return r;
}

int main()
{
  ssa_exprt e;
  e.level = 3;
  auto r = f(e);
  __CPROVER_assert(r.level == 3, "instance re-elaborated when completed");
  return 0;
}
