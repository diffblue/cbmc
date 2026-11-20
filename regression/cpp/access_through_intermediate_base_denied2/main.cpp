// N5008 [class.access.base]/5: m is not accessible in B when named in E,
// nor (/5.4) when named in a base of E accessible in B.
struct A
{
private:
  int m = 1;
};
struct D : public A
{
  friend struct B;
};
struct E : D
{
};
struct B
{
  int get(E &e)
  {
    return e.m; // m is private in A: inaccessible as named in D, too
  }
};
int main()
{
  E e;
  B b;
  return b.get(e);
}
