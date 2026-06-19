// [temp.variadic] / [class.base.init]: a constructor may forward a function
// parameter pack to a base-class initializer.  When the base-initializer
// argument list has a non-pack argument *before* the pack expansion
// (`Base(tag, args...)`), the pack must still be forwarded.  This is exactly
// std::optional's construction shape: the converting constructor delegates to
// `_Optional_base(std::in_place, std::forward<Args>(args)...)`, so getting this
// wrong is why `std::optional<int> o = 5; o.value()` fails (the option ends up
// disengaged / unset).  A member initializer of the same shape already works;
// only the base-class case is affected.

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
  Derived() {}
  template <class... A>
  Derived(tag_t, A... a) : Base<T>(tag_t{}, a...)
  {
  }
};

int main()
{
  Derived<int> d(tag_t{}, 5);
  __CPROVER_assert(d.set, "pack forwarded to base initializer sets the flag");
  __CPROVER_assert(d.value == 5, "pack forwarded to base initializer sets value");
  return 0;
}
