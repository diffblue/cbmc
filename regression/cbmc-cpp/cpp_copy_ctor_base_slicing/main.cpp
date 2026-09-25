// Copying a derived object whose base class has a converting/forwarding
// constructor template.
//
// N5008 [class.copy.ctor]/14: the implicitly-defined copy constructor copies
// each base subobject using that base's copy constructor, applied to the
// corresponding base subobject of the source.  The argument to the base copy
// constructor therefore has the base type.  If the whole derived object were
// passed instead, a forwarding constructor template in the base
// (`Base(U&&)`) would deduce `U` as the derived type and bind it exactly,
// outranking the base copy constructor (which would need a derived-to-base
// conversion) — selecting an unintended constructor whose member initializer
// is then ill-formed.  This must not happen: the copy constructor of the base
// is used, preserving the value.

extern "C" int __VERIFIER_nondet_int();
extern "C" void __CPROVER_assert(int, const char *);

template <typename Head>
struct Base
{
  Head h;
  Base() = default;
  // Converting/forwarding constructor template.
  template <typename U>
  Base(U &&u) : h(u)
  {
  }
};

template <typename T1, typename T2>
struct Wrap : Base<T1>
{
  Wrap() = default;
  Wrap(T1 x) : Base<T1>(x)
  {
  }
};

int main()
{
  int v = __VERIFIER_nondet_int();
  Wrap<int, int> a(v);
  Wrap<int, int> b = a; // copies the Base subobject via Base's copy ctor
  __CPROVER_assert(b.h == v, "base subobject copied by value");
  return 0;
}
