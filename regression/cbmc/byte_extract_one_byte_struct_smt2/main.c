// Regression test for an SMT2 back-end invariant violation
// "TODO typecast8 bv -> struct_tag" in smt2_convt::convert_typecast.
//
// Reading a one-byte aggregate (here a struct of two 4-bit bit-fields)
// through a byte-level access produces, in lower_byte_extract, a
// byte_extract whose result type is a struct occupying a single byte.
// The width==1 fast path of lower_byte_extract used to emit a plain
// typecast(bit-vector -> struct), which the SMT2 back-end cannot encode
// (the SAT back-end flattens it transparently, so only SMT2 solvers --
// the bundled cprover-smt2, Z3, Bitwuzla, cvc5 -- were affected).
//
// With the fix, the single byte is turned into the aggregate via
// bv_to_expr, so the struct is built correctly and the assertion is
// checked normally.

struct two_nibbles
{
  unsigned char lo : 4;
  unsigned char hi : 4;
};

int main(void)
{
  unsigned char byte;
  struct two_nibbles *p = (struct two_nibbles *)&byte;
  __CPROVER_assert(p->lo <= 15, "low nibble is in range");
  return 0;
}
