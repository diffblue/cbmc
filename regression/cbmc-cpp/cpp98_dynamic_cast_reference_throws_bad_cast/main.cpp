// N5008 [expr.dynamic.cast]/10: a failed cast to reference type throws an
// exception of a type that would match a handler of type std::bad_cast
#include <typeinfo>
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  virtual ~A()
  {
  }
};
struct B : A
{
  int b;
};
struct C : A
{
};
int main()
{
  B b;
  C c;
  A &rb = b, &rc = c;
  __CPROVER_assert(&dynamic_cast<B &>(rb) == &b, "reference cast succeeds");
  bool thrown = false;
  try
  {
    (void)dynamic_cast<B &>(rc);
  }
  catch(const std::bad_cast &)
  {
    thrown = true;
  }
  __CPROVER_assert(thrown, "bad_cast thrown");
  __CPROVER_assert(!thrown, "WRONG (must FAIL)");
}
