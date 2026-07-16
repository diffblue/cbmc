// N5008 [temp.variadic]/8: the k-th instantiation of a pack expansion
// substitutes the k-th pack element INTO the pattern -- including the
// pattern's cv-qualifiers.  The pattern of `const Es &... e` is
// `const Es &`; for Tup<int, double, char> the replicated parameters must
// be `const int &, const double &, const char &`.
//
// Regression: the in-class parameter-pack replication replaced the whole
// pattern type with the raw pack element, dropping the pattern's `const`.
// The parameters became non-const `int &, double &, char &`, which cannot
// bind rvalue arguments ([dcl.init.ref]/5), so the only viable constructor
// was wrongly removed from the overload set ("found no match for symbol
// 'Tup'") and main was truncated.  This is the root cause of the
// libstdc++ std::make_tuple arity >= 3 failure (cpp17_tuple_basic):
// tuple's converting constructor `tuple(const _Elements&... __elements)`
// lost its const the same way (the arity <= 2 tuple<_T1,_T2> partial
// specialization took a different path, hence the arity boundary).
//
// g++/clang++ accept and verify the value at runtime.
extern "C" void __CPROVER_assert(int, const char *);

template <typename... Es>
struct Tup
{
  int first;
  Tup(const Es &... e) : first(sum(e...)) {}
  static int sum(int a, double b, char c)
  {
    return a + (int)b + (c == 'a');
  }
};

int main()
{
  // rvalue arguments bind to the constructor only if the replicated
  // parameters keep the pattern's const
  Tup<int, double, char> t(39, 2.0, 'a');
  __CPROVER_assert(t.first == 42, "const pack pattern preserved");
  return 0;
}
