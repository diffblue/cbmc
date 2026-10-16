// N5008 [expr.const]/5, /14: a call of a constexpr function returning a
// class, a temporary built by a constexpr constructor, and member reads and
// member calls on them are constant expressions; [stmt.switch]/2: so is a
// case label built from them (GCC 16's _Escapes<_CharT>::_S_tab()[0] in
// __should_escape_ascii)
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int a;
  int b;
  constexpr int sum() const
  {
    return a + b;
  }
};
constexpr P make()
{
  return P{1, 2};
}
static_assert(make().a == 1, "member of a call result");
static_assert(make().sum() == 3, "member call on a call result");
template <class C>
struct sv
{
  const C *p;
  unsigned long n;
  constexpr sv(const C *s, unsigned long len) : p(s), n(len)
  {
  }
  constexpr sv substr(unsigned long pos, unsigned long len) const
  {
    return sv(p + pos, len);
  }
  constexpr C operator[](unsigned long i) const
  {
    return p[i];
  }
};
static_assert(sv<char>("ab", 2).n == 2, "member of a temporary");
static_assert(sv<char>("ab" + 1, 1)[0] == 'b', "pointer into a literal");
template <class C>
struct esc
{
  static consteval sv<C> all()
  {
    return sv<C>("\t\\t\n\\n", 6);
  }
  static consteval sv<C> tab()
  {
    return all().substr(0, 3);
  }
  static consteval sv<C> newline()
  {
    return all().substr(3, 3);
  }
};
static_assert(esc<char>::newline()[0] == '\n', "consteval chain");
template <class C>
constexpr bool should_escape(C c)
{
  using E = esc<C>;
  switch(c)
  {
  case E::tab()[0]:
  case E::newline()[0]:
    return true;
  default:
    return false;
  }
}
int main()
{
  __CPROVER_assert(
    should_escape('\t') && should_escape('\n'), "case labels evaluated");
  __CPROVER_assert(!should_escape('a'), "default label");
  __CPROVER_assert(should_escape('a'), "WRONG (must FAIL)");
  return 0;
}
