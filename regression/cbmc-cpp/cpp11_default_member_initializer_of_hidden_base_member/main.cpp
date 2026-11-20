extern "C" void __CPROVER_assert(bool, const char *);
struct L
{
  int next = 5;
};
struct D : L
{
  int next = 7; // hides L::next ([class.member.lookup])
};
int main()
{
  D d;
  __CPROVER_assert(d.L::next == 5 && d.next == 7, "each from its own NSDMI");
  __CPROVER_assert(d.L::next == 7, "WRONG (must FAIL)");
}
