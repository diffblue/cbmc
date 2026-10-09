// A variadic function template returning a variadic class template instance
// by value (N5008 [temp.variadic], [stmt.return]).  The function body
// constructs a `box<E...>` and returns it; resolving `box<E...>` while
// type-checking the body must expand the pack `E...` per element rather than
// collapsing it to a single element (which previously left the function with
// no body and an "invalid implicit conversion from box to box").

template <class... E>
struct box
{
  int n;
};

template <class... E>
box<E...> make_box()
{
  box<E...> b;
  b.n = sizeof...(E);
  return b;
}

int main()
{
  box<int, double, char> b3 = make_box<int, double, char>();
  __CPROVER_assert(b3.n == 3, "three elements");

  box<int> b1 = make_box<int>();
  __CPROVER_assert(b1.n == 1, "one element");

  return 0;
}
