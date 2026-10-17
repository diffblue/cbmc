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
  A *p = &d; // [conv.ptr]/3: ambiguous base
  return p->i;
}
