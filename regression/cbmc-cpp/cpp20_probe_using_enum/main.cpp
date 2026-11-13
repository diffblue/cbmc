// N5008 [enum.udecl]: a using-enum-declaration.
extern "C" void __CPROVER_assert(bool, const char *);
enum class E
{
  a,
  b
};
int main()
{
  using enum E;
  E e = b;
  __CPROVER_assert(e == E::b, "using enum");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
