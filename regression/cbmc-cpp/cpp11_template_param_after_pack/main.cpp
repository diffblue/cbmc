// N5008 [temp.param]/11: a template parameter pack of a function template need
// not be the last template parameter -- it may be followed by further template
// parameters provided they are deducible from the parameter-type-list or have
// default template arguments.  Here `first` has a parameter pack `W` followed by
// a defaulted parameter `X`:
//
//   template <class U, class... W, class X = void> int first(U, W...);
//
// A call `first(5, 6, 7)` deduces U=int, W={int,int}, and X=void (its default),
// and returns the first argument.
//
// KNOWNBUG: CBMC's function-template argument deduction mis-handles a template
// parameter that FOLLOWS a parameter pack.  Once the non-empty pack `W` is
// expanded, the deduced template-argument list has more entries than there are
// template parameters, and the default-argument / final matching machinery no
// longer lines the trailing parameter `X` up with its (defaulted) argument, so
// the call is reported as "found no match for symbol 'first'" and the front end
// emits a CONVERSION ERROR.  This is the current root cause of cpp17_tuple_basic
// (std::make_tuple / std::_Tuple_impl select forwarding constructors whose
// template parameter list is `<class _UHead, class... _UTail, class = enable_if_t
// <...>>` -- a parameter after a pack -- so the tuple's element-storing
// constructor body is never instantiated and get<0> reads an uninitialised
// member).  The same shape called from inside another template body drops that
// body entirely ("no body for callee").
//
// Flip to CORE once a template parameter following a parameter pack is deduced
// and instantiated correctly.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

template <class U, class... W, class X = void>
int first(U u, W...)
{
  return u;
}

int main()
{
  __CPROVER_assert(
    first(5, 6, 7) == 5,
    "template parameter following a parameter pack: value deduced/returned");
  __CPROVER_assert(first(5, 6, 7) != 5, "WRONG must FAIL");
  return 0;
}
