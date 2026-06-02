// Overload resolution among function-template overloads must instantiate
// only the SIGNATURE of each candidate; the body (definition) of a
// candidate is instantiated only when that specialization is used, i.e.
// after it has been selected ([temp.inst]/2, [over.match]).
//
// This is the arith_tools `numeric_cast_v` pattern:
//
//   template <typename Target> Target numeric_cast_v(const mp_integer &);
//   template <typename Target> Target numeric_cast_v(const constant_exprt &);
//
// For `numeric_cast_v<mp_integer>(some_constant_exprt)` the second
// overload is an exact match and must be selected.  The first overload is
// non-viable (no constant_exprt -> mp_integer conversion); crucially its
// body `numeric_castt<mp_integer>{}(arg)` is ill-formed for
// Target=mp_integer (numeric_castt<mp_integer> has no operator()(mp_integer)).
//
// CBMC eagerly instantiated the body of the explicitly-named template
// specialization while forming the call's candidate, so the non-selected
// overload's ill-formed body produced a spurious hard error
// ("found no match for symbol 'operator()'") during overload resolution.

struct Expr
{
  int v;
};

struct ConstExpr : Expr
{
  int w;
};

// Stands in for numeric_castt<Target>: only callable with a ConstExpr.
template <typename Target>
struct castt
{
  int operator()(const ConstExpr &c) const
  {
    return c.w;
  }
};

// Overload A: parameter type `Expr` (stands in for mp_integer).  Its body
// is ill-formed for any Target (castt<Target> has no operator()(Expr)).
template <typename Target>
int conv(const Expr &)
{
  Expr e;
  return castt<Target>{}(e);
}

// Overload B: parameter type `const ConstExpr&` — an exact match for a
// ConstExpr argument.  Its body is well-formed.
template <typename Target>
int conv(const ConstExpr &c)
{
  return castt<Target>{}(c);
}

int main()
{
  ConstExpr c;
  c.w = 42;
  // Overload B (exact match) must be selected; overload A is non-viable
  // and its ill-formed body must not be instantiated.
  __CPROVER_assert(conv<int>(c) == 42, "exact-match overload selected");
  return 0;
}
