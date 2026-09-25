// N5008 [dcl.fct]/6 (explicit object parameter), [over.match.funcs]/3 and
// [temp.deduct.call]/1-3: for a member function TEMPLATE whose explicit
// object parameter is a forwarding reference (`this Self &&self'), Self is
// deduced from the object expression (`A &' for an lvalue A) -- the point of
// "deducing this".  Deduction skipped the object argument together with the
// parameter (as for an implicit `this'), so Self was never deduced and the
// call had no viable candidate ("found no match for symbol 'get'"); the
// viability check and the member-call construction likewise dropped the
// object.  libstdc++ 16's std::_Bind::operator()(this _Self &&, _Args &&...)
// is this shape (the gcc16 bind KNOWNBUG; found by its cvise reduction).
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int v = 5;
  template <class Self>
  int get(this Self &&self)
  {
    return self.v;
  }
};
struct B
{
  template <class... Args, class Self>
  int operator()(this Self &&self, Args &&...args)
  {
    return sizeof...(Args) * 10 + 1;
  }
};
struct C
{
  int base = 100;
  template <class... Args, class Self, class NonRef = Self>
  int operator()(this Self &&self, Args &&...args)
  {
    return self.base + sizeof...(Args);
  }
};
int main()
{
  A a;
  B b;
  C c;
  __CPROVER_assert(a.get() == 5, "explicit object parameter");
  __CPROVER_assert(b(1, 2) == 21, "pack before explicit object parameter");
  __CPROVER_assert(c(1, 2, 3) == 103, "with a defaulted parameter after");
  __CPROVER_assert(b() == 1, "empty pack");
  __CPROVER_assert(b(1) == 21, "WRONG (must FAIL)");
}
