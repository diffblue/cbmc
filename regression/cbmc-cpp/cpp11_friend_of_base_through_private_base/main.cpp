// N5008 [class.access.base]/5.4: a member m of a base class B of the naming
// class N is accessible at R only if B itself is accessible at R; per
// [class.access.base]/4 a private base B of D is accessible only in members
// and friends of D.  f is a friend of B, not of D, so `d.m' (named in D) is
// ill-formed.  g++ 13 and clang++ 18 reject it.
struct B
{
protected:
  int m = 3;
  friend int f();
};
struct D : private B
{
};
int f()
{
  D d;
  return d.m;
}
int main()
{
  return f() - 3;
}
