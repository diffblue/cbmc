// N5008 [dcl.init.general]/16.6.2, [class.base.init]/7: `addr({1, 2})'
// initializes the aggregate member addr by its copy/move constructor from a
// temporary initialized by {1, 2}.  The front end tried the parenthesized
// aggregate initialization `addr(1, 2)' with the list as the first element
// first, which printed "invalid implicit conversion from '<<type:>>'" (the
// error was then rolled back, so the program was not rejected).
extern "C" void __CPROVER_assert(bool, const char *);
typedef struct
{
  unsigned long pa, va;
} address_pair_t;
struct prim
{
  address_pair_t addr;
  prim() : addr({1, 2})
  {
  }
};
int main()
{
  prim p;
  __CPROVER_assert(p.addr.pa == 1 && p.addr.va == 2, "member");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
