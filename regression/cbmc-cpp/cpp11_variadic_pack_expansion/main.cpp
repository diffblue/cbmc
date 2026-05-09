// Per [temp.variadic]/5,7: when a pack expansion has zero arguments, the
// expansion is discarded.  CBMC must remove pack-expanded parameters
// and pack references from member initializers and function calls.
//
// Regression for the empty-pack handling in cpp_instantiate_template:
// a constructor template like X(A, Args&&...) called with X(a) must
// be instantiated with Args=<> and the corresponding pack parameter
// removed from the function signature.

template <class A, class... Rest>
struct X
{
  A value;
  int sum;
  X(A a, Rest... rest) : value(a), sum(sum_of(rest...))
  {
  }

private:
  static int sum_of()
  {
    return 0;
  }
  template <class T, class... Ts>
  static int sum_of(T t, Ts... ts)
  {
    return t + sum_of(ts...);
  }
};

int main()
{
  // Empty pack: Rest = <>
  X<int> a(10);
  __CPROVER_assert(a.value == 10, "empty pack: value stored");
  __CPROVER_assert(a.sum == 0, "empty pack: sum_of() base case");

  // Non-empty pack: Rest = <int, int>
  X<int, int, int> b(10, 20, 30);
  __CPROVER_assert(b.value == 10, "non-empty pack: value stored");
  __CPROVER_assert(b.sum == 50, "non-empty pack: sum_of(20, 30) = 50");

  return 0;
}
