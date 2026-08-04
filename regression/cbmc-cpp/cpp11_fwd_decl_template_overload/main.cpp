extern "C" void __CPROVER_assert(bool, const char *);

// libc++ <__fwd/get.h> pattern: the whole `get` overload family is
// forward-DECLARED side by side; definitions follow elsewhere.
template <long, class...> int get(int);
template <int, class> int get(void);
// [dcl.fct]/4: `(void)` declares NO parameters -- distinct from (int)
// even with identical template heads (second cvise harvest).
template <long, class...>
int get(void);

// Same heads and arity but structurally different parameter types
// (third cvise harvest): the by-index get over tuple<_Tp...> must not
// redirect to the tuple<> overload's definition.  Parameter NAMES are
// not signature ([dcl.fct]/5): the unnamed declaration still redirects
// to a definition with named parameters.
template <class...>
struct tuple
{
};
template <long, class... _Tp>
int get(tuple<_Tp...> t);
template <long, class...>
int get(tuple<>)
{
  return 99;
}
template <long, class... _Tp>
int get(tuple<_Tp...> t)
{
  return 31;
}

int x = 5;
int caller() { return get<0>(x); }
int caller2()
{
  return get<0>(tuple<int>{});
}

// definition after the odr-use ([temp.over.link]/6 identity)
template <long, class...> int get(int v) { return v + 2; }

int main()
{
  __CPROVER_assert(caller() == 7, "declared-then-defined overload");
  __CPROVER_assert(caller2() == 31, "tuple overloads distinct");
  return 0;
}
