// N5008 [expr.prim.fold], [temp.variadic]/5, [dcl.type.decltype]: a
// trailing-return-type `-> decltype((a + ...))' over a function parameter
// pack of two or more elements has the type of the expanded fold.  CBMC
// rejects the call (CONVERSION ERROR) for a function template and a member
// function template alike; a one-element pack works.  `sum' and `S::sum'
// worked at 81c536b185 (bin53) and broke before 4810cde624; `sum_ref' never
// worked: the expansion's placeholders for the parameters are prvalues, so
// `g(int &)' does not bind ([expr.prim.id.unqual]/3: a named parameter is
// an lvalue).
extern "C" void __CPROVER_assert(bool, const char *);

int g(int &x)
{
  return x;
}

template <class... A>
auto sum(A... a) -> decltype((a + ...))
{
  return (a + ...);
}

template <class... A>
auto sum_ref(A... a) -> decltype((g(a) + ...))
{
  return (g(a) + ...);
}

struct S
{
  template <class... A>
  auto sum(A... a) -> decltype((a + ...))
  {
    return (a + ...);
  }
};

int main()
{
  __CPROVER_assert(sum(1, 2) == 3, "function template");
  __CPROVER_assert(sum_ref(1, 2) == 3, "lvalue parameters");
  S s;
  __CPROVER_assert(s.sum(1, 2, 3) == 6, "member function template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
