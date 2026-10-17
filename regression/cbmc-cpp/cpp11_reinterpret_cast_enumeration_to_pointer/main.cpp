extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.reinterpret.cast]/5: an enumeration value can be converted to
// a pointer, and [expr.reinterpret.cast]/4 back to a large enough integer
enum class handle : long long
{
  invalid = -1
};
int main()
{
  int x = 0;
  handle h = static_cast<handle>(reinterpret_cast<long long>(&x));
  void *p = reinterpret_cast<void *>(h);
  __CPROVER_assert(p == &x, "enumeration to pointer");
  __CPROVER_assert(
    reinterpret_cast<void *>(handle::invalid) != nullptr, "invalid handle");
  __CPROVER_assert(p == nullptr, "WRONG (must FAIL)");
  return 0;
}
