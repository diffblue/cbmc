// N5008 [expr.mptr.oper]/4: if the dynamic type of the object does not
// contain the member to which the pointer refers the behavior is undefined;
// [class.virtual]/1-2: a call through a pointer to a virtual member function
// is a virtual call -- the final overrider in the object's dynamic type
// runs.  Pointers to virtual member functions were rejected ("pointers to
// virtual methods are currently not implemented"); `&C::vf' now designates
// a thunk that dispatches through the object's virtual table.
extern "C" void __CPROVER_assert(bool, const char *);
int log_v = 0;
struct S
{
  int k;
  virtual int v(int x)
  {
    return k + x;
  }
  virtual void w()
  {
    log_v += 1;
  }
  virtual ~S()
  {
  }
};
struct D : S
{
  int v(int x) override
  {
    return 100 + x;
  }
  void w() override
  {
    log_v += 10;
  }
};
struct E : D
{
  void w() override
  {
    log_v += 100;
  }
};
int apply(S *p, int (S::*pf)(int), int x)
{
  return (p->*pf)(x);
}
int main()
{
  S s;
  s.k = 5;
  D d;
  E e;
  int (S::*pv)(int) = &S::v;
  void (S::*pw)() = &S::w;
  int (D::*pdv)(int) = &D::v; // D's overrider, through D::*
  __CPROVER_assert(
    (s.*pv)(1) == 6 && (d.*pv)(1) == 101 && (e.*pv)(1) == 101,
    "dispatch through S::*");
  (s.*pw)();
  (d.*pw)();
  (e.*pw)();
  __CPROVER_assert(log_v == 111, "void virtual through member pointer");
  __CPROVER_assert((d.*pdv)(2) == 102 && (e.*pdv)(2) == 102, "D::* dispatch");
  __CPROVER_assert(
    apply(&e, pv, 3) == 103 && apply(&s, &S::v, 3) == 8,
    "through function parameter");
  __CPROVER_assert(
    pv == &S::v, "equality of pointers to the same virtual function");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
