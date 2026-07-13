// The GCC `__integer_pack` builtin with a CAST argument, as libstdc++ actually
// writes std::make_integer_sequence:
//   template <class T, T N>
//   using make_integer_sequence = integer_sequence<T, __integer_pack(T(N))...>;
// (note the `T(N)` functional cast).
//
// CORE (was KNOWNBUG): with the cast, `T(N)` is subject to the vexing parse and
// the pack-expansion argument is stored as an `ambiguous` function type (`code`
// returning `__integer_pack`, parameter `T N`), so the earlier plain-call
// __integer_pack expansion missed it and CBMC rejected `__integer_pack`.  Fixed
// by also recognising that ambiguous/function-type shape (count = parameter
// name N, element type = parameter type T).  This greens deduction from the real
// std::make_index_sequence.
//
// __integer_pack is a GCC-only builtin (Clang uses __make_integer_seq), so this
// test is GCC-specific.  g++ compiles and runs these values.
//
// Non-vacuous: each assertion is a concrete function of the generated pack.

#include <utility>

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

// libstdc++ make_integer_sequence shape, with the T(N) cast
template <class T, T N>
using mkseq = iseq<T, __integer_pack(T(N))...>;

template <unsigned long... I>
int sum_impl(iseq<unsigned long, I...>)
{
  return add(I...);
}

// deduction from the REAL std::make_index_sequence / std::index_sequence
template <unsigned long... I>
int real_impl(std::index_sequence<I...>)
{
  return add3(I...);
}

int main()
{
  // mkseq<unsigned long, 2> == iseq<unsigned long, 0, 1>; add(0, 1) == 1
  __CPROVER_assert(
    sum_impl(mkseq<unsigned long, 2>{}) == 1, "cast pack {0,1}: 0+1==1");
  // std::make_index_sequence<3> == index_sequence<0, 1, 2>; add3 == 3
  __CPROVER_assert(
    real_impl(std::make_index_sequence<3>{}) == 3, "real seq {0,1,2}: 0+1+2==3");
  return 0;
}
