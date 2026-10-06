// N5008 [expr.context]/2, [conv.lval]: a discarded-value expression naming a
// non-volatile object is not converted to a prvalue, so `(void)r' does not
// access the object r refers to, even after its lifetime has ended
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int *p = new int(1);
  int &r = *p;
  delete p;
  (void)r;
  __CPROVER_assert(true, "no access");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
