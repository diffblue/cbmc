// N5008 [over.ics.list]/7, [dcl.init.list]/3.5-3.7: `o = {}' considers
// opt::operator=(sym &&) and the implicit copy and move assignment operators.
// Binding `{}' to `sym &&' needs a default constructor of sym, which has
// none, so only the implicit operators are viable, and the move assignment
// from a value-initialized opt is selected.  The viability check counted
// the default constructor of sym's base b1, which the front end copies into
// sym, and then failed hard: "found no match for symbol 'sym'"
// (std::optional<symbol_exprt>'s `inverse_memory_map[0] = {}', CBMC's own
// interpreter.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct sym;
struct opt
{
  int state = 1;
  opt &operator=(sym &&);
};
struct b0
{
};
struct b1 : b0
{
};
struct sym : b1
{
  int id;
  sym(int i) : id(i)
  {
  }
};
opt &opt::operator=(sym &&)
{
  state = 2;
  return *this;
}
int main()
{
  opt o;
  o = {};
  __CPROVER_assert(o.state == 1, "implicit assignment selected");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
