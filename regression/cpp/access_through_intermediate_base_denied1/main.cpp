// N5008 [class.access.base]/5: m is not accessible in B when named in E,
// nor (/5.4) when named in a base of E accessible in B.
struct A
{
protected:
  int m = 1;
};
struct D : private A
{
  friend struct B;
};
struct E : private D
{
};
struct B
{
  int get(E &e)
  {
    return e.m; // D is a private base of E: not accessible in B
  }
};
int main()
{
  E e;
  B b;
  return b.get(e);
}
