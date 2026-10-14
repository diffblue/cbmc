// N5008 [temp.deduct.call]/1: an initializer list argument makes P a
// non-deduced context (unless P is initializer_list<P'> or an array);
// [temp.deduct]/5: the parameter then takes its default template argument.
// `template <class U = T> opt(U &&)' called with `{b, e}' deduces nothing
// and uses U = T -- libstdc++'s optional(_Up &&) with `_Up = _Tp', CBMC's
// own `return {{checked_when_taken, op1}}' (dog-fooding).  U was bound to
// the list's placeholder type and no constructor matched; and a `return'
// of a single braced element that is itself a list did not reach the
// constructor path at all once the aggregate path had declined.
extern "C" void __CPROVER_assert(bool, const char *);
struct chk
{
  bool when;
  int e;
};
template <class T>
struct opt
{
  bool has = false;
  T val{};
  opt() = default;
  template <class U = T>
  opt(U &&u) : has(true), val(static_cast<U &&>(u))
  {
  }
};
opt<chk> get(bool b, int e)
{
  if(b)
    return {{b, e}};
  return {};
}
int main()
{
  opt<chk> o = get(true, 3);
  __CPROVER_assert(
    o.has && o.val.e == 3 && o.val.when,
    "braced list to defaulted deduction parameter");
  opt<chk> p{{false, 7}};
  __CPROVER_assert(p.has && p.val.e == 7, "direct-list-init");
  __CPROVER_assert(!get(false, 0).has, "empty");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
