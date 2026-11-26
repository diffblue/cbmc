// N5008 [class.access.base]/4.3: B is a protected base of D, so in a member
// of E (derived from D) an invented public member of B would be a protected
// member of E: B is accessible there, and D * converts to B *.
extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  int v = 7;
};
struct D : protected B
{
};
struct E : D
{
  int h(D *d)
  {
    B *p = d;
    return p->v;
  }
};
int main()
{
  E e;
  D d;
  __CPROVER_assert(e.h(&d) == 7, "protected base via member of derived");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
