// N5008 [dcl.meaning.general]/1, [basic.scope.param]/1: in
// `auto pipe(X *p) -> decltype(make2(p))', p has type X * -- the
// decl-specifier type modified by the parameter's declarator.  The
// placeholders CBMC declared for the trailing-return-type took the
// decl-specifier type alone, so p was an X and `make2(p)' found no match.
extern "C" void __CPROVER_assert(bool, const char *);

int make2(int *p)
{
  return *p;
}

template <class X>
X take(X &x)
{
  return x;
}

template <class X>
auto pipe(X *p) -> decltype(make2(p))
{
  return make2(p);
}

template <class X>
auto pipe_ref(X &r) -> decltype(take(r))
{
  return take(r);
}

int main()
{
  int x = 7;
  __CPROVER_assert(pipe(&x) == 7, "pointer declarator");
  __CPROVER_assert(pipe_ref(x) == 7, "reference declarator");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
