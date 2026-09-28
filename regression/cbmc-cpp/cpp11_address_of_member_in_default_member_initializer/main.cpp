extern "C" void __CPROVER_assert(bool, const char *);
struct s
{
  int x = 5;
  // N5008 [expr.unary.op]/4: only `&C::m' (a qualified-id) forms a pointer
  // to member; in a default member initializer `x' is `(*this).x'
  // ([expr.prim.id.general]/4), so `&x' is an `int *'
  int *p = &x;
};
int main()
{
  s v;
  __CPROVER_assert(*v.p == 5 && v.p == &v.x, "points to the object's member");
  __CPROVER_assert(*v.p == 6, "WRONG (must FAIL)");
}
