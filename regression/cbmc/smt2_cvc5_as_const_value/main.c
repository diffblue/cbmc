union U
{
  char buf[4];
  unsigned x;
};
struct S
{
  int n;
  union U u;
};
int main()
{
  struct S s;
  s.u.x = 0;
  char c;
  __CPROVER_assume(c == 5);
  s.u.buf[1] = c;
  __CPROVER_assert(s.u.x == 0x500u, "x");
  return 0;
}
