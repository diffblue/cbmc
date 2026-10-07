// N5008 [temp.arg.explicit]/7, [temp.deduct.call]/4: an argument is
// implicitly converted to a parameter type that contains no template
// parameter participating in deduction -- sv<C> of a member template of
// fstr<C>, with C fixed by the class
extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct sv
{
  const C *p;
  sv(const C *q) : p(q)
  {
  }
};
template <class C>
struct fstr
{
  template <class O>
  O format(sv<C> s, O o)
  {
    return o + int(s.p[0]);
  }
  int plain(sv<C> s)
  {
    return int(s.p[0]);
  }
};
int main()
{
  fstr<char> f;
  __CPROVER_assert(f.plain("a") == 97, "non-template member");
  __CPROVER_assert(f.format("a", 1) == 98, "member template");
  __CPROVER_assert(f.format("a", 1) == 97, "WRONG (must FAIL)");
}
