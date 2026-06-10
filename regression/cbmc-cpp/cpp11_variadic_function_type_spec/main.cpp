// [temp.deduct.type]/9-10 and [temp.variadic]/5: a class template partial
// specialization over a function type with a function parameter pack
// (the std::function<R(A...)> pattern) must deduce the pack from the
// argument's parameter list and expand it when the specialization is
// instantiated.  Before the fix, a 0-arg or 2+-arg signature deduced an
// empty (never-elaborated) instance, so e.g. sizeof...(A) was wrong and the
// contextual conversion to bool was rejected.

template <typename>
struct fn_traits;

template <typename R, typename... A>
struct fn_traits<R(A...)>
{
  bool engaged = false;

  // sizeof...(A) read at run time (a static const member initialised with
  // sizeof... is, independently, not constant-folded by CBMC).
  int arity() const
  {
    return sizeof...(A);
  }

  explicit operator bool() const
  {
    return engaged;
  }
};

struct S
{
  int x;
};

int main()
{
  // Deduction of the pack across arities, including the empty pack.
  fn_traits<int()> f0;
  fn_traits<int(int)> f1;
  fn_traits<int(int, char)> f2;
  fn_traits<int(int, char, double)> f3;
  fn_traits<void(const S &)> fr;

  __CPROVER_assert(f0.arity() == 0, "zero-length pack");
  __CPROVER_assert(f1.arity() == 1, "one-element pack");
  __CPROVER_assert(f2.arity() == 2, "two-element pack");
  __CPROVER_assert(f3.arity() == 3, "three-element pack");
  __CPROVER_assert(fr.arity() == 1, "reference parameter pack");

  // The specialization must be elaborated (non-empty), so its explicit
  // operator bool is available for the contextual conversion below.
  int n = 0;
  if(f2)
    n = 1;
  __CPROVER_assert(n == 0, "operator bool elaborated and engaged is false");

  return 0;
}
