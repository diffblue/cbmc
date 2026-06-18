// C++ [temp.deduct.call]/3: when a function parameter is a forwarding
// reference and the corresponding argument is an lvalue of type A, the template
// parameter is deduced as "lvalue reference to A" (A&), so the parameter type
// collapses to A& and binds to the lvalue.  This applies element-wise to a
// forwarding-reference parameter pack (Args&&... args) too.
//
// Regression: the deduction code applied this rule only to a single forwarding
// reference, not to a forwarding-reference *pack*.  For `f(Args&&... args)`
// called with an lvalue, the pack element was deduced as a plain rvalue
// reference (Args=A, parameter A&&), so the parameter bound through a
// dangling/garbage reference and forwarded the wrong value.  Header-free.

template <typename... A>
int first_of(A &&... a)
{
  int arr[] = {a...};
  return arr[0];
}

// Perfect-forwarding through a variadic wrapper to a target that distinguishes
// lvalues from rvalues.
int g(int &) { return 1; }   // lvalue
int g(int &&) { return 2; }  // rvalue
template <typename... A>
int fwd_to_g(A &&... a)
{
  return g(static_cast<A &&>(a)...);
}

int main()
{
  int x = 7;

  // Forwarding-reference pack with an lvalue argument must forward the value.
  __CPROVER_assert(first_of(x) == 7, "fwd-ref pack forwards lvalue value");

  // Forwarding-reference pack with an rvalue argument.
  __CPROVER_assert(first_of(7) == 7, "fwd-ref pack forwards rvalue value");

  // Perfect forwarding preserves the value category: lvalue -> g(int&),
  // rvalue -> g(int&&).
  __CPROVER_assert(fwd_to_g(x) == 1, "fwd-ref pack preserves lvalue category");
  __CPROVER_assert(fwd_to_g(7) == 2, "fwd-ref pack preserves rvalue category");

  return 0;
}
