// N5008 [dcl.fct]/6: the bare `...` (C varargs) parameter must survive
// the empty-pack parameter removal when the trailing template pack
// deduces empty.  Distilled from libc++ __invoke under the ranges
// views::take pipe.  Pre-fix: main silently dropped.
extern "C" void __CPROVER_assert(bool, const char *);
struct bb
{
  int operator()()
  {
    return 7;
  }
} c;
template <class F, class...> decltype(F()()) invoke_(F f, ...)
{
  return f();
}
int arr_;
int main()
{
  __CPROVER_assert(invoke_(c, arr_) == 7, "varargs+pack invoke");
  return 0;
}
