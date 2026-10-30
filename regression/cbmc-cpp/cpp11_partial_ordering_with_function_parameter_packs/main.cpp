// N5008 [temp.deduct.partial]/8, /11 and Example 1, [temp.deduct.type]/10
// and Example 6: in partial ordering a function parameter pack of the
// parameter template takes every remaining type of the argument template;
// a pack of the argument template without a corresponding parameter is
// ignored, and one corresponding to a non-pack parameter makes deduction
// fail; of two templates at least as specialized as each other, the one
// without a trailing function parameter pack is more specialized.
extern "C" void __CPROVER_assert(bool, const char *);

template <class... Args>
int f(Args... args)
{
  return 1;
}
template <class T1, class... Args>
int f(T1 a1, Args... args)
{
  return 2;
}
template <class T1, class T2>
int f(T1 a1, T2 a2)
{
  return 3;
}

template <class T, class... U>
int g(T *, U...)
{
  return 1;
}
template <class T>
int g(T)
{
  return 2;
}

template <class T>
int h(T)
{
  return 1;
}
template <class T, class... U>
int h(T, U...)
{
  return 2;
}

// the same through a using-declaration of a base's member template
struct Base
{
  template <class... Args>
  int operator()(Args...)
  {
    return 1;
  }
};
struct Derived : Base
{
  template <class R, class F>
  int operator()(R, F)
  {
    return 2;
  }
  using Base::operator();
};

int main()
{
  int i = 0;
  __CPROVER_assert(f() == 1, "f(): #1");
  __CPROVER_assert(f(1, 2, 3) == 2, "f(1, 2, 3): #2");
  __CPROVER_assert(f(1, 2) == 3, "f(1, 2): #3");
  __CPROVER_assert(g(&i) == 1, "g(T *, U...) over g(T)");
  __CPROVER_assert(h(1) == 1, "h(T) over h(T, U...)");
  __CPROVER_assert(Derived()(1, 2) == 2, "using-declaration");
  __CPROVER_assert(Derived()(1) == 1, "using-declaration, one argument");
  __CPROVER_assert(f(1, 2) == 2, "WRONG (must FAIL)");
  return 0;
}
