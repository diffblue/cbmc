// N5008 [module.import]: f is visible through the import of module m.
import m;
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(f() == 1, "f from the imported module");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
