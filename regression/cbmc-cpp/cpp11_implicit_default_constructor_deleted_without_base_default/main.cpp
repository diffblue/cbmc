// N5008 [class.default.ctor]/2.3: the implicitly declared default
// constructor of D is defined as deleted when a direct base (or a member of
// class type without a default member initializer) has no usable default
// constructor.  Deletion belongs to the declaration, so
// __is_constructible(D) and `requires { D(); }' are false even though D's
// constructor is never odr-used ([dcl.fct.def.default]/5: it is defined
// only when odr-used).  CBMC declared the constructor and decided its
// deletion only when defining it.
extern "C" void __CPROVER_assert(bool, const char *);

struct B
{
  int n;
  B(int v) : n(v)
  {
  }
};

struct D : B
{
  D(int v) : B(v)
  {
  }
};

struct E : B
{
};

struct M
{
  B b;
};

struct N
{
  B b = B(9);
};

template <class T>
concept default_constructible = requires
{
  T();
};

static_assert(!__is_constructible(E));
static_assert(!default_constructible<E>);
static_assert(!__is_constructible(M));
static_assert(__is_constructible(N));

int main()
{
  D d(3);
  N n;
  __CPROVER_assert(d.n == 3 && n.b.n == 9, "values");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
