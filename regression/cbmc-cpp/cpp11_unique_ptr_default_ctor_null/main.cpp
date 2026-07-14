// N5008 [unique.ptr.single.ctor]/1: the default constructor of
// std::unique_ptr value-initializes the stored pointer -- a default-
// constructed unique_ptr is null.  g++ and clang++ agree (runtime-checked).
//
// KNOWNBUG: cbmc leaves the stored pointer nondet.  unique_ptr's default
// constructor is a *constructor template* (constrained on the deleter):
//   template<typename _Del = _Dp, typename = _DeleterConstraint<_Del>>
//   constexpr unique_ptr() noexcept : _M_t() { }
// Its specialization symbol is created during overload resolution, but with a
// nil body: the inline body is never sourced from the member template of the
// lazily-completed unique_ptr<C> instance (the deferred member-body
// instantiation gap, same family as the map/tuple "no body for callee"
// cases).  The silent nil body makes the constructor call a no-op, so the
// member stays nondet and every unique_ptr value property downstream
// (release/reset/move-assignment, delete preconditions) fails from this one
// root.  Hand-written replications of the constructor-template shape work;
// the trigger needs the real libstdc++ lazy-completion path (cvise reductions
// either drift to a different specialization-matching bug or into UB
// artifacts).  Flip to CORE once member bodies are instantiated on odr-use.

#include <memory>

extern "C" void __CPROVER_assert(int, const char *);

struct C
{
  int v;
  explicit C(int x) : v(x)
  {
  }
};

int main()
{
  std::unique_ptr<C> p;
  __CPROVER_assert(p.get() == nullptr, "default-constructed unique_ptr is null");
  return 0;
}
