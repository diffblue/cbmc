extern "C" void __CPROVER_assert(bool, const char *);

#include <cstddef>
#include <utility>

// [expr.prim.fold]/2: a unary right fold `(E op ...)' is
// `E1 op (... op (EN-1 op EN))', over a non-type template parameter pack of
// a member function template (and of a lambda with a template parameter
// list, whose call operator is one)
template <int... I>
struct seq
{
};

static unsigned long digits;
static void g(int v)
{
  digits = digits * 10 + v;
}

struct folds
{
  template <int... I>
  void right(seq<I...>)
  {
    (g(I), ...);
  }
  template <int... I>
  void left(seq<I...>)
  {
    (..., g(I));
  }
  template <int... I>
  static int right_minus(seq<I...>)
  {
    return (I - ...);
  }
  template <int... I>
  static int left_minus(seq<I...>)
  {
    return (... - I);
  }
};

int main()
{
  folds f;
  f.right(seq<1, 2, 3, 4>{});
  __CPROVER_assert(digits == 1234, "unary right fold over the comma");
  digits = 0;
  f.left(seq<1, 2, 3, 4>{});
  __CPROVER_assert(digits == 1234, "unary left fold over the comma");
  __CPROVER_assert(
    folds::right_minus(seq<1, 2, 3, 4>{}) == -2 &&
      folds::left_minus(seq<1, 2, 3, 4>{}) == -8,
    "subtraction");

  digits = 0;
  [&]<std::size_t... J>(std::index_sequence<J...>)
  { (g(static_cast<int>(J) + 1), ...); }(std::make_index_sequence<4>{});
  __CPROVER_assert(digits == 1234, "lambda with a template parameter list");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
