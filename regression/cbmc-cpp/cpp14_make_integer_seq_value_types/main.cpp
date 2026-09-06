// Companion canary for cpp11_deduced_nontype_kind_mismatch: N5008
// [temp.deduct.type]/17 requires a value deduced for a non-type
// template parameter to have the parameter's type EXACTLY.  Enforcing
// that rule must NOT break THIS valid program: the clang builtin
// __make_integer_seq synthesizes int_seq<unsigned long, 0ul, 1ul>,
// whose values must be recorded with the declared type (unsigned
// long), and deducing `unsigned long... I` from it is exact.  The
// round-44 enforcement attempt failed precisely here: CBMC parks
// deduced values with normalized kinds, so the exact-match check saw a
// spurious mismatch.  Keep this green while flipping the KNOWNBUG.
// (g++ rejects __make_integer_seq -- clang-only shape.)
extern "C" void __CPROVER_assert(bool, const char *);
template <class A, class B> struct is_same_
{
  static const bool value = false;
};
template <class A> struct is_same_<A, A>
{
  static const bool value = true;
};
template <class T, T... I> struct int_seq
{
};
template <unsigned long... I> using indices = int_seq<unsigned long, I...>;
template <unsigned long N>
using make_indices = __make_integer_seq<int_seq, unsigned long, N>;
template <unsigned long... I> bool check(int_seq<unsigned long, I...>)
{
  bool oks[] = {is_same_<decltype(I), unsigned long>::value...};
  bool ok = true;
  for(bool b : oks)
    ok = ok && b;
  return ok;
}
int main()
{
  __CPROVER_assert(
    check(make_indices<2>{}),
    "make_integer_seq values keep the declared type");
  return 0;
}
