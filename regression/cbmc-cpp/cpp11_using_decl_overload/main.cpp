// N5008 [namespace.udecl]/16 with [class.member.lookup]/4: a using-declaration
// `using Base::f;` in a derived class introduces Base's `f` overloads into the
// derived class; they are combined with any derived-class members named `f`
// into a single overload set and are NOT hidden by them.  Only members that are
// merely visible through inheritance (no using-declaration) are hidden when the
// derived class declares its own member of the same name.
//
// This mirrors CBMC's own namespacet hierarchy: namespace_baset declares the
// non-virtual `const symbolt &lookup(const irep_idt&)` alongside the virtual
// `bool lookup(const irep_idt&, const symbolt*&)`, and namespacet re-exposes
// them with `using namespace_baset::lookup;` while overriding the two-argument
// form.  A one-argument call `ns.lookup("x")` must find the inherited
// one-argument overload.  CBMC used to drop the using-imported base overload
// during member resolution -- it applied the [class.member.lookup]/4 hiding
// rule by declaring-class, hiding a base-declared candidate whenever a
// derived-declared candidate of the same name existed, even though the base
// overload was brought in by a using-declaration -- reporting
// "found no match for symbol 'lookup'".
//
// Here `derived_t` re-exposes `base_t::look` via a using-declaration while
// declaring its own two-argument `look`.  The one-argument call `d.look(7)`
// must resolve to the inherited `base_t::look(int)`.  g++ and clang++ accept
// this.
//
// Non-vacuous: assertion.2 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct sym_t
{
  int v;
};

struct base_t
{
  sym_t s;

  // Non-virtual one-argument overload returning a reference, like
  // namespace_baset::lookup(const irep_idt&).
  const sym_t &look(int name) const
  {
    const sym_t *p = nullptr;
    look(name, p);
    return *p;
  }

  // Pure-virtual two-argument overload, like the bool lookup(irep_idt,
  // symbolt*&) form.  Declaring it in the derived class would, without the
  // using-declaration, hide base_t::look(int) by name.
  virtual bool look(int, const sym_t *&) const = 0;
};

struct derived_t : base_t
{
  using base_t::look; // re-expose base_t::look(int) into the overload set

  bool look(int, const sym_t *&p) const override
  {
    p = &s;
    return true;
  }
};

int main()
{
  derived_t d;
  d.s.v = 42;
  const sym_t &r = d.look(7); // must select the inherited base_t::look(int)
  __CPROVER_assert(
    r.v == 42, "one-argument overload via using-declaration resolves");
  __CPROVER_assert(r.v != 42, "WRONG must FAIL");
  return 0;
}
