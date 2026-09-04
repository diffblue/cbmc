// N5008 [temp.local]/1 + [temp.param]/15: inside a member class template
// defined out of line, the member template's OWN parameter is in scope
// for its members -- including as a DEFAULT TEMPLATE ARGUMENT of a
// friend declared inside it:
//   template <class V> template <bool Const>
//   class view_<V>::sentinel_ {
//     template <bool Other = Const> friend bool operator==(...);
//   };
// This is libc++'s take_view::__sentinel shape (the ranges pipe).
// Resolving `Const` throws while the friend is instantiated (the
// enclosing member template's parameter is not bound in that context),
// and main is silently dropped.
// g++ and clang++ both accept (-Werror) and run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct iter_holder
{
  T v_;
  T base() const
  {
    return v_;
  }
};
template <bool, class T> using maybe_const = T;
template <class V> struct view_
{
  V base_;
  template <bool> class sentinel_;
  auto end()
  {
    return sentinel_<true>{};
  }
  auto begin()
  {
    return iter_holder<V>{base_};
  }
};
template <class V>
template <bool Const>
class view_<V>::sentinel_
{
public:
  template <bool Other> using iter_ = iter_holder<maybe_const<Other, V>>;
  // friend whose default template argument names the member class
  // template's OWN parameter
  template <bool Other = Const>
  friend bool operator==(iter_<Other> lhs, sentinel_)
  {
    return lhs.base() == 0;
  }
};
int main()
{
  view_<int> v{0};
  auto b = v.begin();
  auto s = v.end();
  __CPROVER_assert(b == s, "friend default arg names member's own parameter");
  return 0;
}
