// N5008 [dcl.ambig.res]/1: in `int (*p)(A) = k;' with A a type name, (A)
// is a parameter-declaration-clause: p is a pointer to function, not an
// int * initialized from A
extern "C" void __CPROVER_assert(bool, const char *);
using A = long;
struct S
{
  int v;
};
int k(A a)
{
  return int(a) + 1;
}
int m(S *s, A)
{
  return s->v;
}
template <class T>
int call(T t)
{
  int (*q)(T) = k;
  return q(t);
}
int main()
{
  int (*p)(A) = k;
  int (*r)(S *, A) = m;
  S s{7};
  __CPROVER_assert(p(1) == 2, "pointer to int(A)");
  __CPROVER_assert(r(&s, 0) == 7, "pointer to int(S *, A)");
  __CPROVER_assert(call<A>(4) == 5, "pointer to int(T) in a template");
  __CPROVER_assert(p(1) == 1, "WRONG (must FAIL)");
  return 0;
}
