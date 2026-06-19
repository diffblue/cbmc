// [class.inhctor.init] / [namespace.udecl]: an inheriting constructor
// declaration (`using Base::Base;`) makes the base class constructors usable to
// construct the derived class, forwarding the arguments to the corresponding
// base constructor.  CBMC currently detects `using Base::Base;` but skips it
// (inheriting constructors are not implemented), so the derived class is
// constructed by (mistaken) aggregate initialisation and the constructor
// arguments -- here a forwarded parameter pack -- are dropped.

struct tag_t
{
};

template <class T>
struct Base
{
  T value;
  bool set;
  Base() : value(0), set(false) {}
  template <class... A>
  Base(tag_t, A... a) : value(a...), set(true)
  {
  }
};

template <class T>
struct Derived : Base<T>
{
  using Base<T>::Base; // inheriting constructor
};

int main()
{
  Derived<int> d(tag_t{}, 5);
  __CPROVER_assert(d.set, "inheriting constructor sets the flag");
  __CPROVER_assert(d.value == 5, "inheriting constructor forwards the value");
  return 0;
}
