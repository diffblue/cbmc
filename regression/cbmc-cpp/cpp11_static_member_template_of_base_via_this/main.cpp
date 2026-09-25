// N5008 [expr.ref]/6.3, [class.member.lookup]: `this->f<T>(...)' naming a
// STATIC member function template of a BASE class.  The specialization is a
// symbol of the base, not a component of the derived class, so the "must be a
// static component" check rejected it ("is not static member of class") and
// the calling body was dropped -- libc++ std::variant's
// `__assignment::__emplace' calling `__ctor::__construct_alt', three bases up.
extern "C" void __CPROVER_assert(bool, const char *);
struct Base
{
protected:
  template <class T>
  static T &construct(T &slot, T v)
  {
    slot = v;
    return slot;
  }
  static int twice(int x)
  {
    return 2 * x;
  }
};
struct Mid : Base
{
};
struct Derived : Mid
{
  double storage = 0;
  template <unsigned I>
  double &emplace(double v)
  {
    auto &r = this->construct(this->storage, v);
    return r;
  }
  template <class T>
  T &emplace_explicit(T &slot, T v)
  {
    return this->template construct<T>(slot, v);
  }
  int t(int x)
  {
    return this->twice(x);
  }
};
int main()
{
  Derived d;
  d.emplace<1>(2.5);
  __CPROVER_assert(d.storage == 2.5, "deduced static member template of base");
  int slot = 0;
  d.emplace_explicit(slot, 4);
  __CPROVER_assert(slot == 4, "explicit template-id");
  __CPROVER_assert(d.t(3) == 6, "non-template static member of base");
  __CPROVER_assert(d.storage == 1.5, "WRONG (must FAIL)");
}
