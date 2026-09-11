extern "C" void __CPROVER_assert(bool, const char *);
void *operator new(unsigned long, void *) noexcept;
template <typename _Tp, typename... _Args>
_Tp *construct(_Tp *__location, _Args &&...__args)
{
  return ::new((void *)__location) _Tp(static_cast<_Args &&>(__args)...);
}
int main()
{
  int v = 7;
  construct(&v);
  __CPROVER_assert(v == 0, "value-initialized through empty pack");
  return 0;
}
