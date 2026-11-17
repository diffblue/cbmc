// N5008 [dcl.attr.likelihood], [dcl.attr.nouniqueaddr]: [[likely]] and
// [[no_unique_address]] (Itanium C++ ABI layout).
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct S
{
  [[no_unique_address]] E e;
  int x;
};
int main()
{
  int r = 0;
  if(r == 0) [[likely]]
    r = 1;
  __CPROVER_assert(r == 1 && sizeof(S) == sizeof(int), "attributes");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
