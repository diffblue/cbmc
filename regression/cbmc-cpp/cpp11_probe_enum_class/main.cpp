// N5008 [dcl.enum]: a scoped enumeration with a fixed underlying type.
extern "C" void __CPROVER_assert(bool, const char *);
enum class E : char
{
  a = 1,
  b = 2
};
int main()
{
  E e = E::b;
  __CPROVER_assert(
    static_cast<int>(e) == 2 && sizeof(E) == 1, "scoped enumeration");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
