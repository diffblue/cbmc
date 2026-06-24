// N5008 [over.match.class.deduct]/1.1 + [temp.deduct.guide]: when a class
// template has no matching explicit deduction guide, implicit guides are formed
// from its constructors.  The constructor `Wrap(T *p)` yields the guide
// `Wrap(T *) -> Wrap<T>`, so `Wrap w{&x}` with `x` of type `int` deduces
// `Wrap<int>` (T deduced from the pointee), not `Wrap<int *>`.
//
// Regression: CBMC deduced the template parameter positionally from the whole
// argument type (`int *`), giving `Wrap<int *>` and silently mis-typing the
// object; the constructor parameter pattern `T *` was ignored.
template <typename T>
struct Wrap
{
  T val;
  Wrap(T *p) : val(*p) {}
};
int main()
{
  int x; // nondet
  Wrap w{&x};            // implicit guide: Wrap<int>, val = *p
  __CPROVER_assert(w.val == x, "implicit guide Wrap(T*)->Wrap<int>: val == *p");
  return 0;
}
