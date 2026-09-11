// N5008 [temp.variadic]/5 + [expr.new]/1: a new-initializer's
// expression-list is a pack-expansion context; with _Args EMPTY the
// initializer `_Tp(static_cast<_Args&&>(__args)...)` collapses to `_Tp()`.
// Previously the unexpanded pattern made the instantiated body fail
// ("symbol '__args' is unknown") and the callee was silently dropped.
extern "C" void __CPROVER_assert(bool, const char *);
void *operator new(unsigned long, void *) noexcept;
struct markert
{
  int v;
  markert() : v(42)
  {
  }
};
template <typename _Tp, typename... _Args>
_Tp *construct(_Tp *__location, _Args &&...__args)
{
  return ::new((void *)__location) _Tp(static_cast<_Args &&>(__args)...);
}
int main()
{
  markert m;
  m.v = 7;
  construct(&m);
  __CPROVER_assert(m.v == 42, "default-constructed through empty pack");
  return 0;
}
