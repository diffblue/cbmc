struct A
{
  int i;
};
struct B : A
{
};
struct C : A
{
};
struct D : B, C
{
  int f()
  {
    return i; // [expr.prim.id.general]/2, [expr.ref]/8
  }
};
int main()
{
  D d;
  return d.f();
}
