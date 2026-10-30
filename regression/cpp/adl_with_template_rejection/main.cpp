// Test that ADL finds operators in enclosing namespaces and that
// template argument deduction correctly rejects mismatched types.

#include <assert.h>

namespace ns
{
struct S
{
  int val;
};

S operator+(const S &a, const S &b)
{
  S r;
  r.val = a.val + b.val;
  return r;
}

template <typename T>
struct C
{
  T val;
};

// This template should NOT match S arguments.
template <typename T>
C<T> operator+(const C<T> &, const T &)
{
  C<T> r;
  return r;
}
} // namespace ns

int main()
{
  ns::S a, b;
  a.val = 1;
  b.val = 2;
  // ADL should find ns::operator+(S,S), not ns::operator+(C<T>,T)
  ns::S c = a + b;
  assert(c.val == 3);
}
