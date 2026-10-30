extern "C" void __CPROVER_assert(bool, const char *);
// [dcl.fct.default]/4, [temp.mem]/1: the default argument of the in-class
// declaration of a member function template applies to calls of its
// out-of-class definition
struct S
{
  template <class T>
  int m(T, int k = 5);
};
template <class T>
int S::m(T, int k)
{
  return k;
}
int main()
{
  S s;
  __CPROVER_assert(s.m(1) == 5, "member function template");
  __CPROVER_assert(s.m(1) != 5, "WRONG (must FAIL)");
}
