// N5008 [class.virtual]/8-9: called as the final overrider of B::f, a
// covariant D::f's result is converted to B::f's return type.  B is not the
// primary base of D, so the conversion of a D * adjusts it to the B
// subobject ([conv.ptr]/3), a null pointer stays null, and a D & result
// binds as a B & ([dcl.init.ref]/5).
extern "C" void __CPROVER_assert(bool, const char *);
struct Other
{
  virtual int other()
  {
    return 0;
  }
  virtual ~Other() = default;
  int pad = 7;
};
struct B
{
  virtual B *self()
  {
    return this;
  }
  virtual B *none()
  {
    return this;
  }
  virtual B &ref()
  {
    return *this;
  }
  virtual int id()
  {
    return 1;
  }
  virtual ~B() = default;
};
// B is a non-primary base of D: a D * converts to B * with an offset
struct D : Other, B
{
  D *self() override
  {
    return this;
  }
  D *none() override
  {
    return nullptr;
  }
  D &ref() override
  {
    return *this;
  }
  int id() override
  {
    return 2;
  }
};
int main()
{
  D d;
  B &b = d;
  B *as_base = &d;
  __CPROVER_assert(b.self() == as_base, "pointer result converted to B *");
  __CPROVER_assert(b.self()->id() == 2, "converted result designates d");
  __CPROVER_assert(b.none() == nullptr, "null result stays null");
  __CPROVER_assert(&b.ref() == as_base, "reference result converted");
  __CPROVER_assert(d.self() == &d, "direct call");
  __CPROVER_assert(b.self() == nullptr, "WRONG (must FAIL)");
  return 0;
}
