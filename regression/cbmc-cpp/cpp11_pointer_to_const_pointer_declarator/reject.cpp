// N5008 [dcl.ptr]/1, [expr.ass]/1: `*q' is a const pointer -- not an
// assignable lvalue.
int main()
{
  int x = 0;
  int *px = &x;
  int *const *q = &px;
  *q = nullptr;
  return 0;
}
