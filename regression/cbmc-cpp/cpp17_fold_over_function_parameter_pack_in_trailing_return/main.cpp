// N5008 [expr.prim.fold], [temp.variadic]/5, [dcl.type.decltype]: a
// trailing-return-type `-> decltype((a + ...))' over a function parameter
// pack of two or more elements has the type of the expanded fold; each
// element names a parameter, an lvalue ([expr.prim.id.unqual]/3), so
// `g(a)' with `int g(int &)' is well-formed.  CBMC rejected the call once
// any other function template with a pack had been declared (its empty-pack
// entry blocked the fold reduction), and the parameter placeholders of the
// reduction were prvalues.
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

template <class... A>
auto sum_fwd(A &&...a) -> decltype((g(a) + ...))
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
  int x = 4, y = 5;
  __CPROVER_assert(sum_fwd(x, y) == 9, "forwarding references");
  S s;
  __CPROVER_assert(s.sum(1, 2, 3) == 6, "member function template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
