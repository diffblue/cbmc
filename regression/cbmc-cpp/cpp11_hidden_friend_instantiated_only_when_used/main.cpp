extern "C" void __CPROVER_assert(bool, const char *);
// no operator<
struct value
{
  int v;
};
template <class T>
struct tree
{
  T element;
  // libstdc++'s _Rb_tree: a friend function defined in the class template
  // (a "hidden friend").  [temp.inst]/4: its definition is instantiated
  // only if it is odr-used; nothing here compares two trees.
  friend bool operator<(const tree &x, const tree &y)
  {
    return x.element < y.element;
  }
  friend bool operator==(const tree &x, const tree &y)
  {
    return x.element.v == y.element.v;
  }
};
int main()
{
  tree<value> a{{1}}, b{{1}};
  __CPROVER_assert(a == b, "the used friend");
  __CPROVER_assert(a.element.v == 1, "member");
  __CPROVER_assert(!(a == b), "WRONG (must FAIL)");
}
