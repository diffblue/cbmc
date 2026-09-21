// N5008 [temp.variadic]/5 + [expr.prim.req]/2: the requirement
// `::new((void*)0) _Tp(my_declval<_Args>()...)` with _Args deduced
// EMPTY must value-initialize; the unexpanded scalar pattern made the
// constraint read unsatisfied and the calling member's body was
// silently dropped (gcc-16 <optional> _M_apply via std::construct_at).
// Reduced by cvise with a mechanism-pinning gate; see commit message.
extern "C" void __CPROVER_assert(bool, const char *);
void *operator new(unsigned long, void *) noexcept;
template <typename T>
T &&my_declval() noexcept;
template <typename _Tp, typename... _Args>
requires requires
{
  ::new((void *)0) _Tp(my_declval<_Args>()...);
}
constexpr _Tp *my_construct_at(_Tp *__location, _Args &&...__args)
{
  return ::new((void *)__location) _Tp(static_cast<_Args &&>(__args)...);
}
template <typename _Tp>
struct payloadt
{
  _Tp _M_payload;
  bool _M_engaged = false;
  constexpr void _M_apply()
  {
    my_construct_at(&this->_M_payload);
    _M_engaged = true;
  }
};
int main()
{
  payloadt<int> p;
  p._M_apply();
  __CPROVER_assert(p._M_engaged, "constrained callee kept, body converted");
  return 0;
}
