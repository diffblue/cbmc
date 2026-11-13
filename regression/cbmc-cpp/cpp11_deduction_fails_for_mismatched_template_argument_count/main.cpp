// N5008 [temp.deduct.type]/9, [temp.over]/1: deducing P = tup<A> (A not a
// pack) from A = tup<char, char> compares each argument Pi with Ai; the
// argument counts differ, deduction fails, and the template contributes no
// candidate.  The overload with an ellipsis is then the only viable one
// ([over.ics.ellipsis]).  For a member template, the specialization
// instantiated for an earlier call (S(tup<int>)) is not a candidate either:
// it would be viable only through tup's converting constructor template.
extern "C" void __CPROVER_assert(bool, const char *);

template <class... T>
struct tup
{
  template <class... U>
  tup(U...)
  {
  }
};

template <class A>
int f(tup<A>)
{
  return 1;
}

int f(...)
{
  return 2;
}

struct S
{
  int n;
  template <class A>
  S(tup<A>) : n(1)
  {
  }
  S(...) : n(2)
  {
  }
  template <class A>
  int m(tup<A>)
  {
    return 1;
  }
  int m(...)
  {
    return 2;
  }
};

int main()
{
  __CPROVER_assert(f(tup<char, char>()) == 2, "function: before");
  __CPROVER_assert(f(tup<int>()) == 1, "function: deduced");
  __CPROVER_assert(f(tup<char, char>()) == 2, "function: after");
  S a((tup<int>()));
  __CPROVER_assert(a.n == 1 && a.m(tup<int>()) == 1, "member: deduced");
  __CPROVER_assert(a.m(tup<char, char>()) == 2, "member: ellipsis");
  S b((tup<char, char>()));
  __CPROVER_assert(b.n == 2, "constructor: ellipsis");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
