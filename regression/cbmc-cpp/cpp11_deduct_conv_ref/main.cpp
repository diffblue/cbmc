// [temp.deduct.conv]/2 + /4: when the destination type is a
// reference, both the parameter template's reference-typed return
// and the destination reference are stripped before deduction.
//
// This test exercises a `template<class T> operator T&()` template
// conversion operator bound to an `int&` lvalue reference target.
// The deduction should produce T = int, instantiate the operator,
// and the resulting reference should bind so that mutation through
// the reference is visible in the original object.

struct holder
{
  int storage;

  // Template conversion operator returning a reference.
  template <class T>
  operator T &()
  {
    return reinterpret_cast<T &>(storage);
  }
};

int main()
{
  holder h;
  h.storage = 42;

  // Per [temp.deduct.conv] + [over.match.ref]: deduces T = int and
  // binds `r` directly to `h.storage`.
  int &r = h;
  __CPROVER_assert(r == 42, "deduce T = int via operator T&");

  // Mutation through the reference must be visible in the source.
  r = 99;
  __CPROVER_assert(h.storage == 99, "reference binds to source object");

  return 0;
}
