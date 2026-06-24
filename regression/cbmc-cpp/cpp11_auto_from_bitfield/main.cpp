// N5008 [class.bit] + [dcl.type.auto.deduct]: a bit-field has no distinct type
// of its own; reading it yields a prvalue of its underlying type.  `auto x =
// m.b;` therefore deduces the underlying integer type (here unsigned), not a
// bit-field type -- no object may have bit-field type.
//
// KNOWNBUG: CBMC deduced `auto` from the c_bit_field_typet itself; the copied
// bit-field type carried no width, so re-type-checking it reported
// "unexpected expression:" (CONVERSION ERROR).
struct M
{
  unsigned b : 3;
};
int main()
{
  M m;
  m.b = 5;
  auto x = m.b; // x has type unsigned, value 5
  __CPROVER_assert(x == 5, "auto deduced from bit-field holds its value");
  x = x + 2;
  __CPROVER_assert(x == 7, "auto-from-bit-field variable is a full unsigned");
  return 0;
}
