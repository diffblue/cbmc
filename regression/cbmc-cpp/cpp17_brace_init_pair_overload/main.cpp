// Regression for [over.ics.list]/4 element-by-element ICS check on
// brace-init-list to `std::initializer_list<X>`, and [over.match.list]/
// 2.2 fallback to non-init_list constructors of T with brace-init
// elements as args.
//
// Without the fix, a call site like
//   m.insert({key, val})
// where `m` has overloaded `insert` taking `pair_t&&`,
// `const pair_t&`, AND `initializer_list<pair_t>` is rejected with:
//
//   invalid implicit conversion from 'struct K' to 'struct pair_t'
//   invalid implicit conversion from '<<type:>>' to 'struct initializer_list'
//
// because CBMC's overload resolution accepts the
// `insert(initializer_list<pair_t>)` overload as viable without
// checking that each list element converts to `pair_t`.  The "best"
// match becomes `initializer_list<pair_t>` (each `key`, `val` would
// have to be a `pair_t`, which it isn't).
//
// The fix:
//   * `brace_init_to_init_list_is_viable` checks each element has an
//     ICS to the `_begin`/`_M_array` element type before declaring
//     the `initializer_list<X>` overload viable.
//   * `brace_init_is_viable` adds a [over.match.list]/2.2 phase: if
//     no init-list ctor, accept any non-explicit ctor whose required
//     argument count matches the brace-init-list size and whose
//     parameter types each accept the corresponding element via ICS.
//   * The aggregate-style member-wise branch in
//     `cpp_typecheckt::implicit_typecast` now handles
//     reference-to-class targets too.
//   * `cpp_typecheck_fargst::match` biases brace-init candidates
//     with an rvalue-reference target by -1 distance per
//     [over.ics.rank]/3.3.4 so the rvalue-ref overload wins over
//     the const-lvalue-ref overload for prvalue brace-init source.

#include <initializer_list>

struct key_t
{
  int x;
};

struct pair_t
{
  key_t first;
  int second;
  pair_t(const key_t &k, int v) : first(k), second(v)
  {
  }
};

struct map_t
{
  // Mirror the libstdc++ `unordered_map::insert` overload set:
  void insert(const pair_t &)
  {
  }
  void insert(pair_t &&)
  {
  }
  void insert(std::initializer_list<pair_t>)
  {
  }
  // The SFINAE-templated overload from libstdc++ would also be
  // present in real code, but template-argument deduction from a
  // brace-init-list fails per [temp.deduct.call]/1, so it doesn't
  // contribute to overload resolution here.
};

int main()
{
  map_t m;
  key_t k;
  int idx = 0;
  // Brace-init-list `{k, idx}` should select either
  // `insert(const pair_t&)` or `insert(pair_t&&)`, NEVER
  // `insert(initializer_list<pair_t>)` (because `k` is a `key_t`,
  // not a `pair_t`).  The rvalue-ref overload is preferred for
  // a prvalue source per [over.ics.rank]/3.3.4.
  m.insert({k, idx});
  return 0;
}
