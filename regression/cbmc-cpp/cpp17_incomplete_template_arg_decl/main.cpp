// A class template with an INCOMPLETE argument type used only in a
// function DECLARATION.  [temp.inst]/1: a declaration that is not a
// definition does not require the class template specialization to be
// instantiated, so `renamedt<ssa_exprt>` with the merely
// forward-declared ssa_exprt is valid (g++ and clang++ accept).  CBMC
// instantiates the specialization EAGERLY -- including converting the
// constructor -- and hard-errors "invalid initializer 'underlyingt'"
// because the base is incomplete.  Distilled from
// goto-symex/renamed.h + renaming_level.h (the symex_level0 friend
// declaration); blocks dog-fooding every TU that includes
// goto_symex_state.h.  A degenerate variant errors identically even
// when the mem-initializer could never be valid (renamedt<int> with
// `: underlyingt()` and no base at all): the ctor of a
// never-instantiated specialization must not be converted at all.
extern "C" void __CPROVER_assert(bool, const char *);

class ssa_exprt;

template <typename underlyingt>
struct renamedt : private underlyingt
{
  explicit renamedt(underlyingt value) : underlyingt(value)
  {
  }
};

renamedt<ssa_exprt> symex_level0(const ssa_exprt &);

int main()
{
  __CPROVER_assert(true, "trivial");
  return 0;
}
