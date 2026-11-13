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
  A &a = d; // [dcl.init.ref]/5, [conv.ptr]/3: ambiguous base
  return a.i;
}
