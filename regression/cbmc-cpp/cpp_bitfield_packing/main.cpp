// N5008 [class.bit]/1: adjacent bit-fields are packed into the same allocation
// unit; the struct is padded to its alignment ([basic.align]).  Writes to one
// bit-field must not disturb another, and sizeof must reflect the padded ABI
// size.
struct F
{
  unsigned a : 4;
  unsigned b : 4;
  unsigned c : 1;
};
int main()
{
  F f;
  f.a = 9;
  f.b = 15;
  f.c = 1;
  __CPROVER_assert(sizeof(F) == 4, "packed bit-fields have 4-byte ABI size");
  __CPROVER_assert(f.a == 9, "a holds its value");
  __CPROVER_assert(f.b == 15, "b holds its value (independent of a)");
  __CPROVER_assert(f.c == 1, "c holds its value");
  return 0;
}
