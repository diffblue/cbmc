// The GCC `__integer_pack` builtin with a CAST argument, as libstdc++ actually
// writes std::make_integer_sequence:
//   template <class T, T N>
//   using make_integer_sequence = integer_sequence<T, __integer_pack(T(N))...>;
// (note the `T(N)` functional cast).  The direct form `__integer_pack(N)...` is
// handled (cpp17_integer_pack_builtin, CORE), but the cast form takes a
// different path.
//
// KNOWNBUG: with the cast argument, `__integer_pack(T(N))...` is resolved
// eagerly during the alias body's substitution (not as a deferred pack-
// expansion template argument), so it never reaches the typecheck_template_args
// expansion and CBMC rejects `__integer_pack` ("symbol '__integer_pack' is
// unknown"); the body is left incomplete -> VERIFICATION SUCCESSFUL vacuously.
// This is the remaining cpp17_apply_basic blocker: std::apply deduces its
// __apply_impl index_sequence from a make_index_sequence value, whose GCC
// definition uses `__integer_pack(size_t(N))...`.
//
// __integer_pack is a GCC-only builtin; g++ runs r == 1.  Flip to CORE once the
// cast-argument form is expanded (likely by handling __integer_pack where the
// alias body is substituted, mirroring the typecheck_template_args expansion).
//
// Non-vacuous: assertion 2 ("WRONG must FAIL") must FAIL once the pack {0,1} is
// generated and the body is really type-checked.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
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

int main()
{
  int r = sum_impl(mkseq<unsigned long, 2>{});
  __CPROVER_assert(r == 1, "cast __integer_pack yields {0,1}: 0+1==1");
  __CPROVER_assert(r != 1, "WRONG must FAIL");
  return 0;
}
