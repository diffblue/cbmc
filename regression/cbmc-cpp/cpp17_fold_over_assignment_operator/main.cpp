extern "C" void __CPROVER_assert(bool, const char *);
// libstdc++ 16 <format>'s _S_access: a fold over `=' with at most one
// element ([expr.prim.fold]/1, /3: `(e1 op ... op e2)' is a binary fold)
template <typename... V>
int &set(int &x, V... v)
{
  static_assert(sizeof...(V) <= 1, "at most one");
  return (x = ... = v);
}
template <typename... V>
int &add(int &x, V... v)
{
  return (x += ... += v);
}
int main()
{
  int a = 0;
  set(a, 7);
  int b = 1;
  add(b, 2);
  int c = 5;
  set(c);
  __CPROVER_assert(a == 7 && b == 3 && c == 5, "assignment folds");
  __CPROVER_assert(&set(c) == &c, "the result refers to the left operand");
  __CPROVER_assert(b == 1, "WRONG (must FAIL)");
}
