// Constructor variant of cpp17_template_arg_completed_later: the
// specialization instantiated at a declaration-only point (argument
// type INCOMPLETE, [temp.inst]/1 requires nothing) has a constructor
// with a base mem-initializer.  After the argument type is completed
// and the specialization genuinely used ([temp.point]: a new point of
// instantiation), CBMC serves the stale incomplete-base instance;
// this variant reaches symbolic execution and ABORTS on an invariant
// violation in goto_symext::symex_assign (type-inconsistent
// assignment from the stale layout).  g++ and clang++ accept and the
// program verifies at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

class ssa_exprt;

template <typename underlyingt>
struct renamedt : private underlyingt
{
  explicit renamedt(underlyingt value) : underlyingt(value)
  {
  }
  const underlyingt &get() const
  {
    return *this;
  }
};

renamedt<ssa_exprt> symex_level0(const ssa_exprt &);

class ssa_exprt
{
public:
  int level;
  ssa_exprt() : level(0)
  {
  }
};

renamedt<ssa_exprt> symex_level0(const ssa_exprt &e)
{
  return renamedt<ssa_exprt>(e);
}

int main()
{
  ssa_exprt e;
  e.level = 3;
  auto r = symex_level0(e);
  __CPROVER_assert(r.get().level == 3, "stale instance re-elaborated");
  return 0;
}
