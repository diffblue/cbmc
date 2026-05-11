// Regression for the `rebind is ambiguous` front-end bug triggered
// by `std::unordered_map<K, V, Hash>` where Hash is user-defined.
//
// Per [class.member.lookup]/1 and [temp.names]/3, name lookup for
//   _Tp::template rebind<_Up>
// (inside libstdc++'s `std::__alloc_rebind` alias) is restricted to
// the scope of _Tp, and a member declared in a derived class hides
// a member with the same base_name inherited from any base class.
//
// libstdc++'s `std::allocator<T>` inherits from
// `std::__new_allocator<T>`, and both define a `rebind<_Up>` nested
// template.  The derived `allocator::rebind` must hide
// `__new_allocator::rebind` — libstdc++ relies on this to let
// `std::__alloc_rebind<allocator<T>, _Hash_node>` resolve to
// `allocator<_Hash_node>`.
//
// CBMC's `disambiguate_template_classes` previously collected both
// `rebind` templates as primary candidates and errored out with
//   template scope 'rebind' is ambiguous
// The fix narrows candidates by the class-inheritance dominance
// rule: drop any candidate whose declaring class is a base of
// another candidate's declaring class.

#include <unordered_map>

struct key_t
{
  const char *s;
  bool operator==(const key_t &o) const
  {
    return s == o.s;
  }
};

struct key_hasher
{
  std::size_t operator()(const key_t &k) const
  {
    return reinterpret_cast<std::size_t>(k.s);
  }
};

int main()
{
  std::unordered_map<key_t, unsigned, key_hasher> m;
  (void)m;
  return 0;
}
