// N5008 [basic.lookup.argdep]/3: "if the ordinary unqualified lookup of the name
// finds the declaration of a class member function, the associated namespaces
// and classes are not considered."  Furthermore argument-dependent lookup
// considers only namespace-scope functions ([basic.lookup.argdep]/4) -- never
// the member functions of an associated class.
//
// Here the unqualified call `find(s)` inside `C::get` is resolved by ordinary
// unqualified lookup to the member `C::find`, so ADL must not be performed; and
// even if it were, `ns::Str::find` (a member of the argument's class) is not an
// ADL candidate.  The call therefore unambiguously selects `C::find`.
//
// KNOWN BUG: CBMC includes `ns::Str::find` (the argument class's member, callable
// with one argument via its defaulted second parameter) as a candidate, so the
// call "does not uniquely resolve" and conversion fails.  This is the shape of
// `xmlt::get_element`'s `find(element)` (with `element` a `std::string`) being
// made ambiguous with `std::basic_string::find` in src/util/xml.h.
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once
// unqualified lookup that finds a member function suppresses ADL.

extern "C" void __CPROVER_assert(int, const char *);

namespace ns
{
struct Str
{
  // member `find` callable with one argument via the defaulted second
  // parameter -- mirrors std::basic_string::find(const basic_string&, size_t=0)
  unsigned long find(const Str &, unsigned long pos = 0) const { return 0; }
};
} // namespace ns

struct C
{
  int find(const ns::Str &) const { return 42; } // C's own member find
  int get(const ns::Str &s) const { return find(s); }
};

int main()
{
  C c;
  ns::Str s;
  int r = c.get(s);
  __CPROVER_assert(r == 42, "unqualified member find resolves to C::find, not arg-class member");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
