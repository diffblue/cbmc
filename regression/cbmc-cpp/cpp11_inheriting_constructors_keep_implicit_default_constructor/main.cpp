// N5008 [class.default.ctor]/1: if there is no user-declared constructor or
// constructor template for class X, a default constructor is implicitly
// declared; [namespace.udecl]/2: a using-declarator naming a constructor
// inherits the base's constructors, it declares none of X's own.  So `d'
// below has an implicit default constructor (and copy/move constructors).
// When base declares no constructor, CBMC reports "found no match for
// symbol 'd'" for every form of initialization without arguments; with a
// user-declared base constructor it works.  Found while reducing libc++'s
// __bind_back_t (`using __perfect_forward<...>::__perfect_forward').
extern "C" void __CPROVER_assert(bool, const char *);

struct base
{
  int n = 4;
};

struct d : base
{
  using base::base;
};

struct base2
{
  int n = 5;
  base2() = default;
  base2(int v) : n(v)
  {
  }
};

struct d2 : base2
{
  using base2::base2;
};

int main()
{
  d a;
  d b{};
  d c = d();
  __CPROVER_assert(
    a.n == 4 && b.n == 4 && c.n == 4, "base without constructors");
  d2 e;
  d2 f(7);
  __CPROVER_assert(e.n == 5 && f.n == 7, "base with constructors");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
