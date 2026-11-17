// N5008 [class.access.base]/4.3: a base class B of N is accessible at R if
// R occurs in a direct member or FRIEND of a class P derived from N and an
// invented public member of B would be a private or protected member of
// P.  B is a protected base of N, so in f, a friend of P, N * converts to
// B *.  g++ 13 accepts the program; clang++ 18 and 20 reject it ("cannot
// cast 'N' to its protected base class 'B'"), which deviates from /4.3.
extern "C" void __CPROVER_assert(bool, const char *);

struct B
{
  int v = 7;
};
struct N : protected B
{
};
struct P : N
{
  friend int f(N *n);
};

int f(N *n)
{
  B *b = n;
  return b->v;
}

int main()
{
  N n;
  __CPROVER_assert(f(&n) == 7, "friend of derived class");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
