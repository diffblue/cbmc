// N5008 [temp.mem]/1 + [class.nest]/1: a member class template of a
// class template may be defined OUT OF LINE
// (`template<class V> template<bool B>
//  class take_view<V>::__sentinel { ... };`, the libc++ take_view
// sentinel shape).  The out-of-line definition completes the in-class
// declaration.  Previously the front end silently SKIPPED such
// definitions ("we do not support yet"), so instantiating
// `__sentinel<true>{}` failed with "type 'struct nil' is still
// incomplete -- cannot initialize", a hard error that killed the
// whole translation unit.
extern "C" void __CPROVER_assert(bool, const char *);
template <class V> struct take_view
{
  V base_;
  template <bool> class __sentinel;
  auto end()
  {
    return __sentinel<true>{};
  }
};
template <class V> template <bool B> class take_view<V>::__sentinel
{
};
int main()
{
  take_view<int> t{3};
  auto s = t.end();
  __CPROVER_assert(t.base_ == 3, "sentinel");
  return 0;
}
