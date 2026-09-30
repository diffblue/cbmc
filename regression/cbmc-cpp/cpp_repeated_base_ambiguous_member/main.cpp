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
};
int main()
{
  D d;
  return d.i; // [expr.ref]/8: A is an ambiguous base of D
}
