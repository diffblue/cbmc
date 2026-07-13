// The remaining cpp17_apply_basic blocker: the GCC `__integer_pack(N)` builtin.
//
// libstdc++ implements std::make_index_sequence via
//   template <class T, T N>
//   using make_integer_sequence = integer_sequence<T, __integer_pack(N)...>;
// (bits/utility.h, the GCC branch), where `__integer_pack(N)...` is a builtin
// pack-expansion expression producing the integers 0, 1, ..., N-1.  std::apply
// deduces its __apply_impl `index_sequence<_Idx...>` from a
// make_index_sequence<tuple_size_v<...>> value, so it depends on __integer_pack.
//
// KNOWNBUG: CBMC's C++ front-end does not know `__integer_pack` ("symbol
// '__integer_pack' is unknown"), so `mkseq<T, N>` never produces its element
// pack; the alias is left incomplete and any deduction/call through it fails
// ("could not fully type-check 'main'").  In cpp17_apply_basic this error is
// swallowed during the deep decltype/SFINAE resolution of std::apply and
// surfaces downstream as the unresolved `<<type:decltype>>` return type.
//
// __integer_pack is a GCC-only builtin (Clang uses __make_integer_seq), so this
// test is GCC-specific -- matching how CBMC processes g++'s libstdc++ headers.
// g++ compiles and runs r == 1.  Flip to CORE once __integer_pack is supported.
//
// Non-vacuous: assertion 2 ("WRONG must FAIL") must FAIL once __integer_pack
// generates the pack {0,1} and the body is really type-checked.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <class T, T...>
struct iseq
{
};

// libstdc++ make_integer_sequence shape
template <class T, T N>
using mkseq = iseq<T, __integer_pack(N)...>;

template <unsigned long... I>
int sum_impl(iseq<unsigned long, I...>)
{
  return add(I...);
}

int main()
{
  // mkseq<unsigned long, 2> == iseq<unsigned long, 0, 1>; add(0, 1) == 1
  int r = sum_impl(mkseq<unsigned long, 2>{});
  __CPROVER_assert(r == 1, "__integer_pack yields {0,1}: 0+1==1");
  __CPROVER_assert(r != 1, "WRONG must FAIL");
  return 0;
}
