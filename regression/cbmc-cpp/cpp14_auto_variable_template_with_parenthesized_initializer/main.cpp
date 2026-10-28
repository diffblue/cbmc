// N5008 [dcl.type.auto.deduct]/2, [temp.spec.general]/5: a variable
// template declared with a placeholder type and a parenthesized
// initializer; every use of the same specialization denotes the one
// variable of the deduced type.
extern "C" void __CPROVER_assert(bool, const char *);

template <class>
auto vb(7);

template <class T, class U>
constexpr bool same = false;
template <class T>
constexpr bool same<T, T> = true;

int main()
{
  int x = vb<char>;
  __CPROVER_assert(same<decltype(vb<char>), int>, "deduced type");
  __CPROVER_assert(x == 7, "value");
  __CPROVER_assert(x == 0, "WRONG (must FAIL)");
  return 0;
}
