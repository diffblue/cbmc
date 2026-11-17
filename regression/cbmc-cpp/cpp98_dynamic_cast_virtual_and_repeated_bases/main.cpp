// N5008 [expr.dynamic.cast]/9: the run-time check also applies when the
// operand points into a virtual base subobject, and when the most derived
// object has several subobjects of the operand's class
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  virtual ~A()
  {
  }
  int a;
};
struct B : virtual A
{
  int b;
};
struct C : virtual A
{
  int c;
};
struct D : B, C
{
  int d;
};
struct X
{
  virtual ~X()
  {
  }
};
struct L : X
{
  int l;
};
struct R : X
{
  int r;
};
struct M : L, R
{
};
int main()
{
  D d;
  A *pa = &d;
  __CPROVER_assert(dynamic_cast<D *>(pa) == &d, "downcast from a virtual base");
  B b;
  A *pb = &b;
  __CPROVER_assert(dynamic_cast<D *>(pb) == 0, "failing downcast");
  M m;
  X *px = static_cast<L *>(&m);
  __CPROVER_assert(
    dynamic_cast<R *>(px) == static_cast<R *>(&m), "repeated base");
  X *py = static_cast<R *>(&m);
  __CPROVER_assert(
    dynamic_cast<L *>(py) == static_cast<L *>(&m) &&
      dynamic_cast<M *>(py) == &m && dynamic_cast<R *>(py) == &m,
    "containing subobject");
  __CPROVER_assert(dynamic_cast<D *>(pb) != 0, "WRONG (must FAIL)");
}
