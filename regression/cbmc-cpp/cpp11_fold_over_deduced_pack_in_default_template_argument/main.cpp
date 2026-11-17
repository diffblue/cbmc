// N5008 [expr.prim.fold]/2, [temp.deduct.general]/5: a fold over a
// function template's own deduced pack in a following parameter's type
// (`enable_if<(__is_same(int, U) && ...), int>::type = 0') expands over
// the deduced elements when the default is substituted.  It used to stay
// unexpanded and became `true', so the constraint never removed the
// candidate.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};

template <
  class... U,
  typename enable_if<(__is_same(int, U) && ...), int>::type = 0>
int f(U...)
{
  return 1;
}
int f(...)
{
  return 2;
}

template <
  class... U,
  typename enable_if<(true && ... && __is_same(int, U)), int>::type = 0>
int g(U...)
{
  return 1;
}
int g(...)
{
  return 2;
}

struct S
{
  int which;
  template <
    class... U,
    typename enable_if<(__is_same(int, U) && ...), int>::type = 0>
  S(U...) : which(1)
  {
  }
  S(double) : which(2)
  {
  }
};

int main()
{
  char *p = nullptr;
  __CPROVER_assert(f(p) == 2, "unary fold removes the candidate");
  __CPROVER_assert(f(1, 2) == 1, "unary fold keeps the candidate");
  __CPROVER_assert(g(p) == 2, "binary fold removes the candidate");
  __CPROVER_assert(g(1) == 1, "binary fold keeps the candidate");
  static_assert(!__is_constructible(S, char *), "constructor removed");
  S s{1};
  __CPROVER_assert(s.which == 1, "constructor kept");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
