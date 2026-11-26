// N5008 [class.copy.assign]/12, [class.copy.ctor]/14: the implicit copy
// assignment and copy constructor of an empty class copy its subobjects,
// of which it has none.  An empty base subobject has zero size
// ([intro.object]/8) and shares its address with the first member: storing
// the class's byte of storage would overwrite that member's.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct D : E
{
  char c;
};
int main()
{
  D d;
  d.c = 'x';
  E &b = d;
  __CPROVER_assert((void *)&b == (void *)&d.c, "empty base at offset 0");
  b = E{};
  E copy(b);
  __CPROVER_assert(d.c == 'x', "storing an empty base writes nothing");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
