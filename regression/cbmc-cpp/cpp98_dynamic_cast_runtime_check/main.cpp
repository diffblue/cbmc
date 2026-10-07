// N5008 [expr.dynamic.cast]/4, /9-10: the result of dynamic_cast<C *>(v),
// C not a base of the class of *v, depends on the most derived object: a
// pointer to its unique public C subobject (down- or cross-cast), else null
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  virtual ~A()
  {
  }
  int a;
  A() : a(1)
  {
  }
};
;
struct B
{
  virtual ~B()
  {
  }
  int b;
  B() : b(2)
  {
  }
};
;
struct D : A, B
{
  int d;
};
struct E : D
{
  int e;
};
struct P : A, private B
{
};
struct Q : A
{
};
int main()
{
  D d;
  E e;
  P p;
  Q q;
  A *pa = &d, *pe = &e, *pp = &p, *pq = &q, *pn = 0;
  __CPROVER_assert(dynamic_cast<B *>(pa) == static_cast<B *>(&d), "cross-cast");
  __CPROVER_assert(
    dynamic_cast<B *>(pe) == static_cast<B *>(&e), "cross-cast, deeper");
  __CPROVER_assert(
    dynamic_cast<D *>(pe) == static_cast<D *>(&e),
    "downcast to an intermediate class");
  __CPROVER_assert(dynamic_cast<E *>(pa) == 0, "downcast failing");
  __CPROVER_assert(dynamic_cast<B *>(pp) == 0, "private base");
  __CPROVER_assert(dynamic_cast<B *>(pq) == 0, "no such base");
  __CPROVER_assert(dynamic_cast<B *>(pn) == 0, "null");
  B *pb = &e;
  __CPROVER_assert(
    dynamic_cast<A *>(pb) == static_cast<A *>(&e) &&
      dynamic_cast<E *>(pb) == &e,
    "from the second base");
  __CPROVER_assert(dynamic_cast<E *>(pa) != 0, "WRONG (must FAIL)");
}
