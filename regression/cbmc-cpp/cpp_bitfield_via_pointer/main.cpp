// N5008 [class.bit]/1 + [basic.align]/1: a bit-field following an ordinary
// member is placed in a later allocation unit; the object has its full ABI
// size, so reading a bit-field through a pointer is in bounds and the
// preceding ordinary member is unaffected.
struct G
{
  int tag;
  unsigned flag : 1;
  unsigned kind : 3;
};
static unsigned get_kind(const G *g)
{
  return g->kind;
}
int main()
{
  G g;
  g.tag = 7;
  g.flag = 0;
  g.kind = 5;
  __CPROVER_assert(get_kind(&g) == 5, "read bit-field through pointer");
  __CPROVER_assert(g.tag == 7, "preceding non-bit-field member intact");
  return 0;
}
