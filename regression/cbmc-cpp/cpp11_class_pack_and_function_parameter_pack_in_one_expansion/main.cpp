// N5008 [temp.variadic]/5: the k-th element of a pack expansion
// instantiates the pattern with the k-th element of EVERY pack it names.
// In `two(get<Is>(vs)...)' the pattern names the enclosing class
// template's non-type pack Is and the member function's parameter pack vs;
// the expansion is {get<1>(vs0), get<2>(vs1)}.  libc++'s
// __dispatcher<_Is...>::__dispatch (std::visit) has this shape.
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long N, class T>
int get(T t)
{
  return t + (int)N;
}

int two(int a, int b)
{
  return a * 10 + b;
}

template <unsigned long... Is>
struct dispatcher
{
  template <class... Vs>
  static int dispatch(Vs... vs)
  {
    return two(get<Is>(vs)...);
  }
};

int main()
{
  __CPROVER_assert(dispatcher<1, 2>::dispatch(3, 4) == 46, "dispatch");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
