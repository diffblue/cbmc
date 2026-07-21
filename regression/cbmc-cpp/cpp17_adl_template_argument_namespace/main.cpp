extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [basic.lookup.argdep]/2: the associated namespaces of a class
// template specialization include the namespaces of its TEMPLATE
// ARGUMENTS.  `transform(w)` must find inner::transform through
// wrapper<inner::elem>'s argument.  CBMC's ADL used not to traverse
// template arguments (fixed 2026-07-21): "symbol 'transform' is unknown", and the
// enclosing function is silently truncated (vacuous success).  The
// shape of unqualified `transform(s.begin(), ...)` over
// __gnu_cxx::__normal_iterator<char*, std::basic_string<...>>, which
// blocks dog-fooding src/goto-cc/goto_cc_main.cpp.
// g++/clang++ accept and verify at runtime.

namespace inner
{
struct elem
{
  int v;
};
template <typename W>
int transform(W w)
{
  return w.t.v + 1;
}
} // namespace inner

namespace outer
{
template <typename T>
struct wrapper
{
  T t;
};
} // namespace outer

int main()
{
  outer::wrapper<inner::elem> w{{41}};
  // `transform` lives in inner, associated ONLY as the namespace of the
  // wrapper's template argument ([basic.lookup.argdep]/2)
  __CPROVER_assert(transform(w) == 42, "ADL via template argument");
  return 0;
}
