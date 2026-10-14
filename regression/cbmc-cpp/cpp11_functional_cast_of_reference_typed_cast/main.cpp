// N5008 [expr.type.conv]/2, [expr.type]/1: in the functional cast `T(e)'
// an operand of reference type -- `static_cast<S &>(x)' -- denotes the
// referred object.  The check for an explicit conversion function of the
// operand's class took the type of e without removing the reference and
// failed an invariant (to_struct_tag_type on a pointer type; CBMC's own
// parse.cpp, `code_frontend_declt(static_cast<symbol_exprt &>(...))',
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct expr
{
  int id;
};
struct symbol_expr : expr
{
};
struct decl
{
  int v;
  explicit decl(symbol_expr s) : v(s.id)
  {
  }
};
struct declaration : expr
{
};
decl make(declaration &d)
{
  // a functional cast whose operand is a cast to a reference type
  return decl(static_cast<symbol_expr &>(static_cast<expr &>(d)));
}
int main()
{
  declaration d;
  d.id = 6;
  __CPROVER_assert(make(d).v == 6, "T(static_cast<S &>(x))");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
