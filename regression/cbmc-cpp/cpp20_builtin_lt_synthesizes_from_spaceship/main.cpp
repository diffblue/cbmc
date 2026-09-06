// clang >= 22 provides the builtin type predicate
// __builtin_lt_synthesizes_from_spaceship(T, U), and libc++ >= 22 uses
// it in __utility/default_three_way_comparator.h whenever
// __has_builtin says it exists.  CBMC preprocesses with the SYSTEM
// compiler, whose __has_builtin answers for itself -- so against
// libc++-22 the header takes the builtin branch and CBMC's parser
// fails ("parse error before 'const _LHS & ,'").  Any <string> /
// <map>-including test breaks in an archlinux (clang 22) container.
// This kernel is self-gating: hosts whose preprocessor lacks the
// builtin compile the #else branch and pass trivially.
extern "C" void __CPROVER_assert(bool, const char *);
struct pt
{
  int v;
  bool operator<(const pt &o) const
  {
    return v < o.v;
  }
};
#if defined(__has_builtin) && __has_builtin(__builtin_lt_synthesizes_from_spaceship)
template <class L, class R>
struct synth
{
  static const bool value =
    __builtin_lt_synthesizes_from_spaceship(const L &, const R &);
};
const bool r = synth<pt, pt>::value;
#else
const bool r = false;
#endif
int main()
{
  __CPROVER_assert(r == r, "spaceship-synthesis builtin parses");
  return 0;
}
