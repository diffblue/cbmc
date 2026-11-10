extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct type_identity
{
  typedef T type;
};
template <class T>
using type_identity_t = typename type_identity<T>::type;
template <class E>
struct view
{
  E *p;
  unsigned n;
  // libstdc++'s span(type_identity_t<element_type> (&)[N]) constructor:
  // [expr.static.cast]/7 with [conv.array], the array converts to a pointer
  template <unsigned N>
  view(type_identity_t<E> (&arr)[N]) : p(static_cast<E *>(arr)), n(N)
  {
  }
};
int main()
{
  char buf[4] = {'a', 'b', 'c', 'd'};
  view<char> v(buf);
  __CPROVER_assert(v.p == buf && v.n == 4, "array to pointer in static_cast");
  __CPROVER_assert(v.n == 3, "WRONG (must FAIL)");
}
