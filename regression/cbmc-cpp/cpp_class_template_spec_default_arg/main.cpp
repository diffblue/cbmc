// An explicit (full) specialization of a class template whose primary
// has a defaulted template parameter must be selected when the class is
// named with the default applied.
//
// For
//   template <typename T, typename = void> struct caster { ... };
//   template <> struct caster<Big> { int operator()(int) const; };
// a use `caster<Big>` resolves to `caster<Big, void>` ([temp.arg]/2:
// the trailing default argument is applied).  The explicit
// specialization is written with the single argument <Big>, but its
// effective argument list is <Big, void> ([temp.class.spec.match]); it
// must therefore match the use.
//
// CBMC compared the use's completed argument list <Big, void> (two
// arguments) against the specialization's written list <Big> (one
// argument), found the sizes unequal, discarded the specialization, and
// fell back to the (empty) primary template — so the member
// `operator()` was not found ("symbol 'operator()' is unknown").
//
// This is the std::optional / arith_tools `numeric_castt` pattern:
//   template <typename Target, typename = void> struct numeric_castt {};
//   template <> struct numeric_castt<mp_integer> { ... };
// which made `numeric_cast<mp_integer>(...)` fail to instantiate.

struct Big
{
  int v;
};

template <typename T, typename = void>
struct caster
{
};

template <>
struct caster<Big>
{
  int operator()(int x) const
  {
    return x + 1;
  }
};

template <typename T>
int cast(int a)
{
  return caster<T>{}(a);
}

int main()
{
  // Both a direct use and a use through an enclosing template must
  // select the explicit specialization.
  caster<Big> c;
  __CPROVER_assert(c(41) == 42, "direct use selects specialization");
  __CPROVER_assert(cast<Big>(41) == 42, "dependent use selects specialization");
  return 0;
}
