// N5008 [class.access.base]/4.3: B is a PRIVATE base of N, so an invented
// public member of B has no access in P (derived from N): in f, a friend of
// P, B is not accessible and N * does not convert to B *.  g++ 13 and
// clang++ 18 reject the program.
struct B
{
  int v = 7;
};
struct N : private B
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
  return f(&n);
}
