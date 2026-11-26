// N5008 [temp.param]/17: the default template arguments of a function
// template are merged from all its declarations; a definition that follows
// a declaration with `typename = ...' does not repeat it, and may name its
// parameters differently.  The definition replaced the
// declaration and the default was lost, so every call that relied on it
// found no match (cvise reduction of libc++'s std::visit, whose declaration
// has `typename = void_t<decltype(__as_variant(declval<_Vs>()))...>').
extern "C" void __CPROVER_assert(bool, const char *);
template <class...>
using void_t = void;
template <class V, class... Vs, typename = void_t<>>
int visit(V &&, Vs &&...);
template <class V, class... Vs, typename>
int visit(V &&, Vs &&...vs)
{
  return 1 + sizeof...(vs);
}
template <class T, typename = void>
int g(T);
template <class T, typename>
int g(T)
{
  return 7;
}
template <class T, class = T *>
int h(T);
template <class U, class D>
int h(U)
{
  return sizeof(D);
}
int main()
{
  __CPROVER_assert(visit(1) == 1, "pack, then default");
  __CPROVER_assert(visit(1, 2, 3) == 3, "non-empty pack");
  __CPROVER_assert(g(1) == 7, "default declared once");
  __CPROVER_assert(h(1) == sizeof(int *), "renamed parameter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
