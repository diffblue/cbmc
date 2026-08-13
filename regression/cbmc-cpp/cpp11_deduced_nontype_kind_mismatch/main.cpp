// Rejects-invalid: N5008 [temp.deduct.type]/17 -- the value deduced
// for a non-type template parameter pack must have the TYPE of the
// parameter (after conversion per [temp.arg.nontype]); deducing
// `long... _Uf` from `indices<0ul, 1ul>` (parameters of type unsigned
// long) is a deduction failure, so no constructor matches and the
// program is ill-formed.  g++ and clang++ both reject ("deduced
// non-type template argument does not have the same type as the
// corresponding template parameter").  CBMC currently ACCEPTS and
// verifies successfully.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long...> struct indices
{
};
struct impl
{
  int n;
  // deducing long... _Uf from indices<unsigned long...> arguments:
  // [temp.deduct.type]/17 -- the deduced value's type must match the
  // corresponding template parameter's type EXACTLY (long != unsigned
  // long), so this candidate never matches.
  template <long... _Uf> impl(indices<_Uf...>) : n(sizeof...(_Uf))
  {
  }
};
int main()
{
  indices<0ul, 1ul> idx;
  impl i(idx);
  __CPROVER_assert(i.n == 2, "should not typecheck");
  return 0;
}
