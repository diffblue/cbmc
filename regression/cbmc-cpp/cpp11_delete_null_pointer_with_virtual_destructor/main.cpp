extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.delete]/5: deleting a null pointer value invokes no
// destructor; with a virtual destructor that call would read the vtable
// pointer through the null pointer (the MSVC STL's ~locale deletes the
// possibly null result of _Decref)
struct B
{
  virtual ~B()
  {
  }
};
struct D : B
{
};
B *make(bool b)
{
  return b ? new D : nullptr;
}
bool nondet_bool();
int main()
{
  bool c = nondet_bool();
  B *p = make(c);
  delete p;
  B *q = nullptr;
  delete q;
  __CPROVER_assert(true, "deleted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
