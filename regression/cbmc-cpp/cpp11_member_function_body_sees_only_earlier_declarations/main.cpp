// N5008 [basic.lookup.unqual]/4, [class.mem.general]/7, [basic.lookup.argdep]
// /4: a member function body defined in its class is looked up as if it
// followed the class definition, so a namespace-scope function declared
// after the class is not a candidate, also not through argument-dependent
// lookup.  The front end converts such bodies at the end of the translation
// unit and found the later overloads too: the call was ambiguous (h(view) and
// h(const later &), CBMC's own util/string_hash.h + dstring.h,
// unit-proofs/escape) or chose a later one.
extern "C" void __CPROVER_assert(bool, const char *);
struct view
{
  const char *p;
};
struct str
{
  const char *p;
  operator view() const
  {
    return view{p};
  }
};
int h(view)
{
  return 1;
}
struct hasher
{
  int operator()(const str &s) const
  {
    return h(s);
  }
};
struct later
{
  later(const str &)
  {
  }
};
int h(const later &)
{
  return 2;
}
// an exact match, but declared too late for hasher's body as well
int h(const str &, int = 0)
{
  return 3;
}
int call_after(const str &s)
{
  return h(s);
}
int main()
{
  str s{"a"};
  __CPROVER_assert(hasher{}(s) == 1, "only h(view) is visible in the body");
  __CPROVER_assert(call_after(s) == 3, "visible after its declaration");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
