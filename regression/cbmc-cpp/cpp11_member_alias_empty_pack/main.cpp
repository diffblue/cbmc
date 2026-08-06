// N5008 [temp.variadic]/7: a trailing template parameter pack that
// matched ZERO arguments is still deduced -- to the empty sequence.
// A member alias template of such an instance (libc++'s
// __integer_sequence<size_t>::__to_tuple_indices<0>, i.e. `iseq<size_t>`
// with `Vs = {}` here) must expand `(Vs + S)...` to nothing; the
// enclosing-parameter pre-bind stopped before the pack parameter when
// the argument list was exhausted, leaving the pack UNBOUND, and the
// bare pack-name resolution then failed -- silently dropping the whole
// enclosing function body (the std::tuple constructor's mem-init
// shape; here, main itself).
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
template <size_t...> struct idx {};
template <class T, T... Vs> struct iseq
{
  template <size_t S>
  using to_idx = idx<(Vs + S)...>;
};
template <size_t... Is> int len(idx<Is...>) { return sizeof...(Is); }
int main()
{
  // the enclosing instance's pack Vs is EMPTY: to_idx<0> = idx<>
  iseq<size_t>::to_idx<0> v;
  __CPROVER_assert(len(v) == 0, "zero indices");
  return 0;
}
