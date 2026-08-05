// Clang's __make_unsigned/__make_signed type builtins, the
// compiler-accelerated backing of N5008 [meta.trans.sign] (libc++'s
// __make_unsigned_t in __lower_bound/__half_positive reaches it for
// every <vector>/<map>/<string> algorithm).  clang builtins => CLANG
// mode (--stdlib libc++).
extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp> using __make_unsigned_t = __make_unsigned(_Tp);
template <class _Tp> using __make_signed_t = __make_signed(_Tp);
enum class E : short { a = 1 };
int main() {
  __make_unsigned_t<int> u = 4000000000u;
  __make_signed_t<unsigned long> s = -5;
  __make_unsigned_t<E> eu = 65535;
  __CPROVER_assert(u == 4000000000u, "u");
  __CPROVER_assert(s == -5, "s");
  __CPROVER_assert(eu == 65535, "eu");
  __CPROVER_assert(sizeof(u) == sizeof(int), "wu");
  __CPROVER_assert(sizeof(eu) == sizeof(short), "we");
  return 0;
}
