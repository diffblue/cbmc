extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.ambig.res]/3, Example 3: a type-name nested in parentheses in a
// parameter-declaration-clause is a simple-type-specifier, so f's parameter
// is a pointer to function int(C), not an int named C; a name that is not a
// type is a parenthesized declarator-id
class C
{
};
int f(int(C))
{
  return 1;
}
int g(C)
{
  return 2;
}
int k(int(x))
{
  return x;
}
int main()
{
  __CPROVER_assert(f(g) == 1 && k(3) == 3, "pointer to function parameter");
  __CPROVER_assert(f(g) != 1, "WRONG (must FAIL)");
}
