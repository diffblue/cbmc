// [class.inhctor.init] / [namespace.udecl]: an inheriting constructor
// declaration (`using Base::Base;`) makes the base class constructors usable to
// construct the derived class, forwarding the arguments to the corresponding
// base constructor.  This includes the base's constructor *templates*
// ([namespace.udecl]/2) -- here a forwarding constructor with a parameter
// pack.  Fixed by registering the base's constructor-template ids in the
// derived class's scope (so overload resolution instantiates them and the
// base subobject is initialized by the selected base constructor) and by not
// treating a class with inherited constructors as an aggregate
// ([dcl.init.aggr]/1, C++17).

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
