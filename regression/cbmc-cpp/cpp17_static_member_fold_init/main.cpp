// N5008 [temp.variadic]/5 + [expr.prim.fold]: a fold expression whose
// pattern is a QUALIFIED reference to a member of each pack element
// (`Ts::v`) substitutes the k-th element INTO the pattern -- the trailing
// `::v` must survive the substitution.
//
// Regression: the class-body fold expander replaced the whole qualified
// name `Ts::v` with the element type, so a static data member initializer
// `static inline int value = (Ts::v + ...)` became a bare type expression;
// symex then crashed on the type-inconsistent assignment (invariant
// "assignments must be type consistent", goto_symex.cpp).  A static
// CONSTEXPR member with the same fold took a different (working) path,
// which masked the defect.
//
// g++/clang++ accept and verify all values at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct A
{
  static constexpr int v = 40;
};
struct B
{
  static constexpr int v = 2;
};

// unary right fold over Ts::v, arities 1 and 2
template <typename... Ts>
struct sum_holder
{
  static inline int value = (Ts::v + ...);
};

// binary fold, seeded ([expr.prim.fold]/2 left association)
template <typename... Ts>
struct seeded_holder
{
  static inline int value = (100 + ... + Ts::v);
};

int main()
{
  __CPROVER_assert(sum_holder<A, B>::value == 42, "arity 2 sum");
  __CPROVER_assert(sum_holder<A>::value == 40, "arity 1 sum");
  __CPROVER_assert(seeded_holder<A, B>::value == 142, "binary seeded");
  return 0;
}
