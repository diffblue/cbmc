// N5008 [class.access.base]/4: a private base B of D is accessible only in
// members and friends of D (/4.2), or of classes derived from D when B's
// invented public member would be protected or private there (/4.3).  A
// member of B itself is neither, so converting D * to B * in B::g is
// ill-formed ([conv.ptr]/3).  g++ 13 and clang++ 18 reject it.
struct B
{
  int m = 3;
  int g();
};
struct D : private B
{
};
D dd;
int B::g()
{
  B *p = &dd;
  return p->m;
}
int main()
{
  return 0;
}
