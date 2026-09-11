// N5008 [dcl.fct]/6 + [temp.variadic]/1: `_Fn...` with a NON-pack _Fn
// declares `_Fn, ...` (a deducible parameter followed by C varargs),
// not a function parameter pack.  Deduce _Fn from the first argument;
// extra arguments bind to the varargs.  Kernel of libc++'s reduced
// __bind_back shape (the ranges pipe operator chain).
extern "C" void __CPROVER_assert(bool, const char *);
template <class _Fn>
int first_of(_Fn __f...)
{
  return __f;
}
int main()
{
  __CPROVER_assert(first_of(42, 1.5) == 42, "P... deduces P from arg0");
  return 0;
}
