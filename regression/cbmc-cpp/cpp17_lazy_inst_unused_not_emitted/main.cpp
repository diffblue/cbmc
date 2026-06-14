// KNOWNBUG / Option B target for N5008 [temp.inst]/11: an unused non-virtual
// member function must NOT be instantiated.  CBMC currently eagerly
// instantiates unused member bodies (via instantiate_template's deferred-method
// loop), so unused()'s body -- including its assertion -- enters the goto
// program (vacuously SUCCESS, since the function is never called).  The
// assertion message therefore appears in the output today.
//
// Under correct lazy, on-odr-use instantiation (Option B), unused() is never
// instantiated and the "must never appear" assertion must not show up at all.
// This test forbids that message; it is KNOWNBUG until Option B lands, then
// becomes CORE.
//
// It is also a precise lazy-vs-eager discriminator: unlike the
// cpp17_lazy_inst_unused_* guards (whose ill-formed bodies merely get their
// conversion error swallowed), here instantiation is observable in the output.

template <class T>
struct S
{
  T v;
  void use() { v = v; }
  void unused() { __CPROVER_assert(0, "must never appear"); }
};

int main()
{
  S<int> s;
  s.v = 1;
  s.use();
  __CPROVER_assert(s.v == 1, "v preserved");
  return 0;
}
