// N5008 [expr.prim.fold] + [temp.variadic]/5: a fold expression over a
// function parameter pack in a MEMBER function template's body is expanded,
// when the member template is instantiated, into the correctly-associated
// binary expression over the pack's elements ([expr.prim.fold]/1-2), with
// the operator identity for an empty pack ([expr.prim.fold]/3).
//
// Regression: member function template bodies are prepared by a different
// (deferred-drain) pack-expander than free function templates, and that
// member-body expander used not to reduce fold expressions -- so the fold's
// bare pack reference (e.g. `a` in `(a + ...)`) was left unexpanded, failed
// to resolve, and the whole body was dropped ("no body for callee").  The
// enclosing class need not be a template.  All values below are verified at
// runtime by g++ and clang++.
extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  // unary right fold: e0 op (e1 op (... op eN-1))
  template <typename... A>
  static int rsum(A... a)
  {
    return (a + ...);
  }
  // unary right fold with a non-associative operator: 40 - 2 == 38
  template <typename... A>
  static int rsub(A... a)
  {
    return (a - ...);
  }
  // unary left fold with a non-associative operator: (100 - 1) - 2 == 97
  template <typename... A>
  static int lsub(A... a)
  {
    return (... - a);
  }
  // binary (init) fold, always left-associated: (100 - a0) - a1
  template <typename... A>
  static int bsub(A... a)
  {
    return (100 - ... - a);
  }
  // empty-pack unary folds yield the operator identity
  template <typename... A>
  static bool all_true(A... a)
  {
    return (a && ...);
  }
  template <typename... A>
  static bool any_true(A... a)
  {
    return (a || ...);
  }
};

// the enclosing class need not be a template, but it may be
template <typename X>
struct T
{
  template <typename... A>
  static int rsum(A... a)
  {
    return (a + ...);
  }
};

int main()
{
  // multi-element (N>=2)
  __CPROVER_assert(S::rsum(40, 2) == 42, "right + fold, arity 2");
  __CPROVER_assert(S::rsum(1, 2, 3, 4) == 10, "right + fold, arity 4");
  __CPROVER_assert(S::rsub(40, 2) == 38, "right - fold, arity 2");
  __CPROVER_assert(S::lsub(100, 1, 2) == 97, "left - fold, arity 3");
  __CPROVER_assert(S::bsub(40, 2) == 58, "binary - fold, arity 2");

  // single element (N==1): the fold is the sole pattern
  __CPROVER_assert(S::rsum(42) == 42, "right + fold, arity 1");
  __CPROVER_assert(S::bsub(40) == 60, "binary - fold, arity 1");

  // empty pack (N==0): the operator identity ([expr.prim.fold]/3)
  __CPROVER_assert(S::all_true(), "empty && fold identity is true");
  __CPROVER_assert(!S::any_true(), "empty || fold identity is false");
  __CPROVER_assert(S::bsub() == 100, "binary fold empty pack yields init");

  // fold in a member template of a class template
  __CPROVER_assert(T<int>::rsum(10, 20, 12) == 42, "fold in class template");

  return 0;
}
