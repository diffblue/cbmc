extern "C" void __CPROVER_assert(bool, const char *);
// [dcl.fct.default]/1,4: the default argument of the first declaration applies
// to calls after the definition, which repeats the declaration without it
// (libstdc++ 13's __format::__do_vformat_to(_Out, ..., const locale * =
// nullptr), called by vformat_to with three arguments)
template <class T>
int f(T, const int * = 0);
template <class T>
inline int f(T, const int *p)
{
  return p ? 2 : 1;
}
template <class U>
int g(U u)
{
  return f(u);
}
// the same for a namespace member defined by a qualified name
// ([dcl.meaning.general]/3.1)
namespace n
{
template <class T>
int h(T, int = 7);
}
template <class T>
int n::h(T, int k)
{
  return k;
}
int main()
{
  __CPROVER_assert(f(1) == 1, "direct call");
  __CPROVER_assert(g(1) == 1, "call from a template");
  __CPROVER_assert(n::h(1) == 7 && n::h(1, 8) == 8, "namespace member");
  __CPROVER_assert(f(1) != 1, "WRONG (must FAIL)");
}
