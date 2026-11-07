// N5008 [expr.add]/5.1: if P and Q both evaluate to null pointer values,
// P - Q is 0 (libstdc++'s vector::_M_realloc_insert computes it for an
// empty vector); [expr.rel]/5: two null pointers compare equal, so p < q is
// false (basic_filebuf::_M_terminate_output tests pbase() < pptr())
extern "C" void __CPROVER_assert(bool, const char *);
// functions with C++ language linkage (main has C language linkage in
// CBMC, and its pointer checks follow C)
long difference(char *p, char *q)
{
  return p - q;
}
bool less(char *p, char *q)
{
  return p < q;
}
int main()
{
  __CPROVER_assert(difference(nullptr, nullptr) == 0, "null minus null");
  __CPROVER_assert(!less(nullptr, nullptr), "null less than null");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
