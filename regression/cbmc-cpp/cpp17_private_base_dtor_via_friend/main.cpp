// Test: derived class can access private base destructor when the base
// class declares the derived class as a friend.  This pattern is used by
// libstdc++'s `std::pair`, which inherits from `std::__pair_base` and is
// declared as a template-friend of `__pair_base`.  Private members of
// `__pair_base` (its destructor in particular) must remain accessible to
// `pair`'s implicit destructor synthesis, otherwise pair fails to
// elaborate as a struct tag.
//
// The bug: the access-check fallback that allowed derived-class access
// to base-class members built the expected struct_tag identifier as
// `tag-<qualified_name>`, but the actual stored identifier puts the
// `tag-` prefix AFTER the enclosing namespace
// (`<namespace>::tag-<class_name>`).  The mismatched comparison meant
// the derived-from check never matched, and the access was rejected.

namespace ns {

template <typename _T1, typename _T2>
struct pair;

template <typename U1, typename U2>
class __pair_base
{
  template <typename _T1, typename _T2> friend struct pair;
  __pair_base() = default;
  ~__pair_base() = default;
  __pair_base(const __pair_base&) = default;
  __pair_base& operator=(const __pair_base&) = delete;
};

template <typename _T1, typename _T2>
struct pair : public __pair_base<_T1, _T2>
{
  _T1 first;
  _T2 second;
};

} // namespace ns

int main()
{
  ns::pair<int, int> p;
  __CPROVER_assert(1, "pair-with-private-base-destructor elaborates");
  return 0;
}
