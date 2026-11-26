extern "C" void __CPROVER_assert(bool, const char *);
int order[4];
int count = 0;
int note(int v)
{
  order[count++] = v;
  return v;
}
// N5008 [expr.prim.fold]: binary folds over the comma operator
template <class... A>
int *last(A... a)
{
  return (nullptr, ..., a); // ((nullptr, a1), a2), ...
}
template <class... A>
int right(A... a)
{
  return (note(a), ..., 9); // note(a1), (note(a2), 9)
}
template <class... A>
int left(A... a)
{
  return (note(0), ..., note(a));
}
int x, y;
int main()
{
  __CPROVER_assert(last(&x, &y) == &y, "binary left fold value");
  __CPROVER_assert(right(1, 2) == 9, "binary right fold value");
  __CPROVER_assert(order[0] == 1 && order[1] == 2, "right fold order");
  count = 0;
  __CPROVER_assert(left(3, 4) == 4, "binary left fold");
  __CPROVER_assert(
    order[0] == 0 && order[1] == 3 && order[2] == 4, "left fold order");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
