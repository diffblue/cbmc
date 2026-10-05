// N5008 [class.base.init]/7, [dcl.init.general]/9: the mem-initializer
// `B()' value-initializes the base; B has no user-provided constructor,
// so it is zero-initialized
extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  long value;
  int k;
};
struct D : B
{
  D() : B()
  {
  }
};
struct E : B
{
  int own;
  E() : B(), own()
  {
  }
};
int main()
{
  D d;
  __CPROVER_assert(d.value == 0 && d.k == 0, "base");
  E e;
  __CPROVER_assert(e.value == 0 && e.own == 0, "base and member");
  __CPROVER_assert(d.value != 0, "WRONG (must FAIL)");
}
