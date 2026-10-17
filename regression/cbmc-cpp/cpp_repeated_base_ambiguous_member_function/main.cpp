struct A
{
  int i;
  int get() const
  {
    return i;
  }
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
  return d.get(); // [expr.ref]/8
}
