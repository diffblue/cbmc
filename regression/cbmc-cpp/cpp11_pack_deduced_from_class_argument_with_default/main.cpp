// N5008 [temp.deduct.type]/9, [temp.param]/14, [temp.variadic]/8: in
// `template <class... U, int N = sizeof...(U)> int count(const tup<U...> &)'
// U is deduced from the class template argument, and the default template
// arguments that follow are substituted afterwards with all of U's elements.
// CBMC counted only function-parameter-pack elements: sizeof...(U) was 0,
// and with two or more elements the slot of a defaulted parameter after U
// was misplaced, so the call found no match.  libc++'s converting
// constructor tuple(const tuple<_Up...> &) is constrained this way.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool B, class T = void>
struct enable_if
{
};

template <class T>
struct enable_if<true, T>
{
  using type = T;
};

template <class... T>
struct tup
{
  int which = 0;
  tup() = default;
  template <
    class... U,
    typename enable_if<sizeof...(U) == sizeof...(T), int>::type = 0>
  tup(const tup<U...> &) : which(1)
  {
  }
};

template <class... U, int N = sizeof...(U)>
int count(const tup<U...> &)
{
  return N;
}

int main()
{
  tup<int, char> t2;
  __CPROVER_assert(count(t2) == 2, "two elements");
  __CPROVER_assert(count(tup<>()) == 0, "empty");
  tup<int> a;
  tup<long> b(a);
  __CPROVER_assert(b.which == 1, "converting constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
