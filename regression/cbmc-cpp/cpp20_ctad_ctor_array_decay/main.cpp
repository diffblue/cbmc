// N5008 [over.match.class.deduct]/1.1 + [temp.deduct.call]/2: each
// CONSTRUCTOR of the class template yields a hypothetical deduction
// guide, and deduction against it follows function-call rules -- for
// the by-value parameter `I i`, an argument of type int(&)[1] DECAYS
// to int*.  CBMC deduced wrap<int[1]> instead of wrap<int*>; the
// mistyped member then crashed simplify_rec downstream
// (simplify_expr.cpp postcondition: array-typed expression simplified
// to non-array).  This was the ranges pipe's last blocker
// (counted_iterator(base_, count_) with base_ = int(&)[1]).
extern "C" void __CPROVER_assert(bool, const char *);
template <class I> struct wrap
{
  wrap(I i, int) : cur_(i)
  {
  }
  I cur_;
};
template <class V> struct holder
{
  V base_;
  auto make()
  {
    return wrap(base_, 1);
  }
};
int main()
{
  int arr[1]{3};
  holder<int(&)[1]> h{arr};
  auto w = h.make();
  int *p = w.cur_;
  __CPROVER_assert(p[0] == 3, "ctor CTAD decays ref-array member");
  return 0;
}
