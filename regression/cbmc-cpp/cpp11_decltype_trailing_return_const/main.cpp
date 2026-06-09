#include <cassert>

struct S
{
  int v;
  int &get() { return v; }
  const int &get() const { return v; }
};

// Trailing-return decltype referencing the function parameter: the
// deduced return type must follow the cv-qualification of the argument
// (const S selects `const int &get() const`, S selects `int &get()`).
// Per [dcl.type.simple]/[over.match.funcs] the implicit object
// parameter's cv-qualifiers participate in overload resolution, and the
// deduction must be performed independently for each instantiation.
template <typename T>
auto comp(T &s) -> decltype(s.get())
{
  return s.get();
}

int main()
{
  S ms{};
  ms.v = 1;

  // Instantiate the non-const specialisation first: it must return a
  // writable int&.
  comp(ms) = 99;
  assert(ms.v == 99);

  // Then the const specialisation: it must return const int& and must
  // NOT reuse the previous instantiation's (non-const) deduced type.
  const S cs{};
  const int &r = comp(cs);
  assert(r == 0);

  return 0;
}
