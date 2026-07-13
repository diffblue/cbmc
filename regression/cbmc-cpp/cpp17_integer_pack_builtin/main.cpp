// The GCC `__integer_pack(N)` builtin: in a pack-expansion `__integer_pack(N)...`
// it produces the integers 0, 1, ..., N-1.  libstdc++ implements
// std::make_index_sequence via `integer_sequence<T, __integer_pack(N)...>` on
// GCC (the extension backing [intseq.make]).
//
// CORE (was KNOWNBUG): CBMC's C++ front-end rejected `__integer_pack` ("symbol
// '__integer_pack' is unknown").  Fixed by detecting a pack-expansion template
// argument that is a call to __integer_pack with a constant count and expanding
// it to N non-type arguments 0..N-1 (of the argument's type), before the
// per-argument type-check.
//
// __integer_pack is a GCC-only builtin (Clang uses __make_integer_seq), so this
// test is GCC-specific -- matching how CBMC processes g++'s libstdc++ headers.
// g++ compiles and runs these values.
//
// Non-vacuous: each assertion is a concrete function of the generated pack.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
}

template <class T, T...>
struct iseq
{
};

// libstdc++ make_integer_sequence shape (direct)
template <class T, T N>
using mkseq = iseq<T, __integer_pack(N)...>;

// nested-alias form
template <unsigned long N>
using mkidx = mkseq<unsigned long, N>;

template <unsigned long... I>
int sum_impl(iseq<unsigned long, I...>)
{
  return add(I...);
}

template <unsigned long... I>
int sum3_impl(iseq<unsigned long, I...>)
{
  return add3(I...);
}

int main()
{
  // mkseq<unsigned long, 2> == iseq<unsigned long, 0, 1>; add(0, 1) == 1
  __CPROVER_assert(sum_impl(mkseq<unsigned long, 2>{}) == 1, "pack {0,1}: 0+1==1");
  // mkidx<3> == iseq<unsigned long, 0, 1, 2>; add3(0, 1, 2) == 3
  __CPROVER_assert(
    sum3_impl(mkidx<3>{}) == 3, "nested-alias pack {0,1,2}: 0+1+2==3");
  return 0;
}
