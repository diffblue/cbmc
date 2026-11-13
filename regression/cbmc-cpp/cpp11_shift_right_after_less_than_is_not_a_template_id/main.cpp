// N5008 [temp.names]/3-4: `<' after a name that is not a template-name is
// the less-than operator; only when it opens a template-argument list may
// a `>>' be treated as two closing `>'.  The parser tries a template-id
// speculatively for an unknown name and split the `>>' of `x < 8 && 2u >>
// 1' into `> >' to close the guessed list; restoring the token position
// did not undo the split, and the expression parse then failed ("parse
// error before '> 1 ; }'"; CBMC's own cpp_typecheck_stdlib.cpp, `bit < 8 ?
// (1u << bit) << 8 : (1u << bit) >> 8', dog-fooding).  Template-ids that
// do close with `>>' still parse.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct box
{
  T v;
};
template <int N>
struct num
{
  static const int value = N;
};
unsigned isbit(int bit)
{
  return bit < 8 ? (1u << bit) << 8 : (1u << bit) >> 8;
}
int main()
{
  int x = 3;
  unsigned a = x < 8 && 2u >> 1;
  unsigned b = x < 8 ? 1u : 2u >> 1;
  auto f = [](int k) -> unsigned { return k < 8 ? 1u : (1u << k) >> 8; };
  box<box<int>> nested{{7}};
  int c = num<(16 >> 2)>::value;
  __CPROVER_assert(
    isbit(0) == 256 && isbit(9) == 2, "conditional with a shift");
  __CPROVER_assert(a == 1 && b == 1 && f(9) == 2, "less-than then shift");
  __CPROVER_assert(nested.v.v == 7 && c == 4, "template-ids closed by >>");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
