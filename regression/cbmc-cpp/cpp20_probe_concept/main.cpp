// N5008 [temp.constr]: overload resolution with a constrained template.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept Small = sizeof(T) <= 2;
template <Small T>
int f(T)
{
  return 1;
}
int f(...)
{
  return 2;
}
int main()
{
  __CPROVER_assert(f('c') == 1 && f(1.0) == 2, "constrained overload");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
