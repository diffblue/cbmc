extern "C" void __CPROVER_assert(bool, const char *);
typedef long long intptr_t;
enum class handle : intptr_t
{
  invalid = -1
};
// N5008 [dcl.init.list]/3.8: direct-list-initialization of an enumeration
// with a fixed underlying type from a single value v of an integral type
// gives the value T(v) (C++17; no narrowing here)
struct file
{
  handle raw;
  explicit file(void *h) : raw{reinterpret_cast<intptr_t>(h)}
  {
  }
};
enum small : unsigned char
{
  zero
};
int main()
{
  int x;
  file f(&x);
  handle h{-1};
  handle g = handle{7};
  small s{3};
  __CPROVER_assert(f.raw == handle(reinterpret_cast<intptr_t>(&x)), "member");
  __CPROVER_assert(h == handle::invalid, "variable");
  __CPROVER_assert(
    g == static_cast<handle>(7) && s == static_cast<small>(3),
    "functional cast and unscoped enumeration");
  __CPROVER_assert(h != handle::invalid, "WRONG (must FAIL)");
  return 0;
}
