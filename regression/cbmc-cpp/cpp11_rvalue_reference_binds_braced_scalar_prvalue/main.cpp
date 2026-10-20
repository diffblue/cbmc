extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U = T>
T exchange(T &v, U &&n)
{
  T old = static_cast<T &&>(v);
  v = static_cast<U &&>(n);
  return old;
}
using pointer = int *;
// N5008 [expr.type.conv]/2, [dcl.init.ref]/5.3.1, [conv.rval]: `pointer{}'
// is a prvalue null pointer; the rvalue reference binds to a temporary
// materialized from it (the MSVC STL's `exchange(_Ptr, pointer{})' in
// std::list's node insertion)
int main()
{
  int x = 1;
  int *p = &x;
  int *q = exchange(p, pointer{});
  int i = 5;
  exchange(i, int{7});
  __CPROVER_assert(p == nullptr && q == &x && i == 7, "temporary bound");
  __CPROVER_assert(p == &x, "WRONG (must FAIL)");
  return 0;
}
