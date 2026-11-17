// N5008 [over.match.viable]/3: a function whose associated constraints are
// not satisfied is not a viable candidate.  In `iterator(iterator<!Const>
// i) requires Const' (the converting constructor of a ranges iterator,
// libc++'s transform_view::__iterator) the constraint depends on the class
// template argument only: iterator<false> has no such constructor to
// offer.  The trailing requires-clause of a constructor was skipped by the
// parser, so iterator<false>'s copy considered converting from
// iterator<true>, whose constructor copies an iterator<false> ... and the
// front end recursed until it crashed.  The satisfaction is checked when
// the constructor is a candidate ([temp.inst]/17).
extern "C" void __CPROVER_assert(bool, const char *);

template <bool Const>
struct iterator
{
  int cur;
  iterator() = default;
  iterator(int c) : cur(c)
  {
  }
  iterator(iterator<!Const> i)
    requires Const
    : cur(i.cur + 1)
  {
  }
};

int main()
{
  iterator<false> it = 3;
  iterator<true> cit = it;
  __CPROVER_assert(it.cur == 3, "plain");
  __CPROVER_assert(cit.cur == 4, "converted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
