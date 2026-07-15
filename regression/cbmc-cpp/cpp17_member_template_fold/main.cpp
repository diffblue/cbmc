// N5008 [expr.prim.fold] + [temp.variadic]/5: a fold expression `(a + ...)`
// over a function parameter pack in a MEMBER function template's body must
// be expanded, when the member template is instantiated, into the
// left-/right-associated binary expression over the pack's elements
// (`a$0 + a$1` for a two-element pack).
//
// KNOWNBUG: the body of a member function template is prepared by a
// different (deferred-drain) pack-expander than a free function template,
// and that member-body expander does not handle fold expressions.  So the
// fold is left unexpanded, the bare pack name `a` fails to resolve, the
// member's body is dropped ("no body for callee S::sum"), and the call
// returns nondet.  The FREE-function-template flavour of the identical
// fold works (the instantiate_template body expander has fold handling);
// only the member flavour is affected -- the enclosing class need not even
// be a template.
//
// g++/clang++ verify the assertion (fold-verified at runtime).  Flip to
// CORE when the member-function-template body expander expands fold
// expressions like the free-function one does.
extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  template <typename... A>
  static int sum(A... a)
  {
    return (a + ...);
  }
};

int main()
{
  __CPROVER_assert(S::sum(40, 2) == 42, "fold over member-template pack");
  return 0;
}
