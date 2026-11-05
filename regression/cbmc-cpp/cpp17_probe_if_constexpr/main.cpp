// N5008 [stmt.if]: if constexpr selecting a branch per instantiation.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
int f(T)
{
  if constexpr(sizeof(T) == 1)
    return 1;
  else
    return 2;
}
int main()
{
  __CPROVER_assert(f('c') == 1 && f(1) == 2, "if constexpr");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
