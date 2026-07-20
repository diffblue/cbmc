// N5008 [temp.deduct]/8: while matching an overloaded candidate, an
// invalid type or expression formed by the substituted template
// arguments is a deduction failure that removes the candidate from
// the overload set -- not a hard error.  Here `get<I1>` in the
// pack-expanded mem-initializer must skip the by-TYPE `get<T>`
// overload (the pack element 0 is no type) and select the by-index
// overload, mirroring std::get's overload set.
//
// This used to fail: substituting the constant into the by-type
// candidate's parameter hard-errored ("expected type, but got
// expression" via an unresolved-name path), aborting resolution of
// the viable by-index overload; the constructor body was dropped.
//
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct tup
{
  int v;
};

template <unsigned long I>
int get(tup &t)
{
  return t.v;
}

template <typename T>
T get(tup &t)
{
  return t.v;
}

template <unsigned long... I>
struct idx
{
};

struct prt
{
  int first;
  template <unsigned long... I1>
  prt(tup &t1, idx<I1...>) : first(get<I1>(t1)...)
  {
  }
};

int main()
{
  tup t{7};
  prt p(t, idx<0>());
  __CPROVER_assert(p.first == 7, "by-index overload selected");
  return 0;
}
