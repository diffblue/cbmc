// N5008 [class.access.base]/5.4: `e.m' names m in class E.  D is a public
// base of E, accessible in B, and m named in D is a private member of D (A
// is a private base of D) -- accessible in B, a friend of D.  So the access
// is valid; g++ and clang++ accept it.  The front end flattens A's members
// into E as inaccessible ("noaccess") and rejects it: "member 'A::m' is not
// accessible (noaccess)".
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
protected:
  int m = 1;
};
struct D : private A
{
  friend struct B;
};
struct E : D
{
};
struct B
{
  int get(E &e)
  {
    return e.m;
  }
};
int main()
{
  E e;
  B b;
  __CPROVER_assert(b.get(e) == 1, "access through the friend of D");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
