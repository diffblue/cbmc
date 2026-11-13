struct E
{
  int v;
  explicit E(int q) : v(q)
  {
  }
};
int main()
{
  // [over.match.copy]/1.1, [class.conv.ctor]/2: an explicit constructor is
  // not a candidate in copy-initialization
  E e = 1;
  return e.v;
}
