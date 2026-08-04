extern "C" void __CPROVER_assert(bool, const char *);

// libc++ <__fwd/get.h> pattern: the whole `get` overload family is
// forward-DECLARED side by side; definitions follow elsewhere.
template <long, class...> int get(int);
template <int, class> int get(void);

int x = 5;
int caller() { return get<0>(x); }

// definition after the odr-use ([temp.over.link]/6 identity)
template <long, class...> int get(int v) { return v + 2; }

int main()
{
  __CPROVER_assert(caller() == 7, "declared-then-defined overload");
  return 0;
}
