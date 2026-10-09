// [temp.deduct.partial]/3.2 + [over.match.best]/2: when multiple
// conversion-function templates are viable for a given destination
// type, partial ordering on their return types picks the most-
// specialised one.
//
// Here `any_t` has two convertible patterns:
//   template<class T> operator T()   — return T (matches anything)
//   template<class U> operator U*()  — return U* (matches pointers)
//
// For `int x = a;`, only `operator T()` is viable (U* cannot match
// a non-pointer destination).  No partial ordering needed.
//
// For `int *p = a;`, both deduce successfully (T = int*, U = int),
// so partial ordering compares them.  `operator U*()` is more
// specialised than `operator T()` (U* fits inside T but T does not
// fit inside U*), so `operator U*()` is selected.

struct any_t
{
  int stored;

  template <class T>
  operator T() const
  {
    return T(stored);
  }

  template <class U>
  operator U *() const
  {
    return nullptr;
  }
};

int main()
{
  any_t a;
  a.stored = 42;

  // Only `operator T()` is viable.  T = int.
  int x = a;
  __CPROVER_assert(x == 42, "deduce T = int via operator T()");

  // Both templates deduce; partial ordering picks `operator U*()`.
  // U = int.  The instantiation returns nullptr.
  int *p = a;
  __CPROVER_assert(p == nullptr, "partial ordering picks operator U*()");

  return 0;
}
