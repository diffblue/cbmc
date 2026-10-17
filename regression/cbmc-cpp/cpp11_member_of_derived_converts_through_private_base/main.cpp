// N5008 [class.access.base]/4.3: B is a PRIVATE base of D; in a member of E
// (derived from D) an invented public member of B would have no access, so
// B is not accessible and D * does not convert to B *.  g++ 13 and
// clang++ 18 reject the program.
struct B
{
};
struct D : private B
{
};
struct E : D
{
  void h(D *d)
  {
    B *p = (B *)nullptr;
    p = d;
  }
};
int main()
{
  return 0;
}
