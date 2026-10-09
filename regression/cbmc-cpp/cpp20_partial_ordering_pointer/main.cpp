// N5008 [temp.func.order] / [temp.deduct.partial]: when two viable function
// template specializations have indistinguishable conversion sequences for the
// call arguments, the more specialized template is chosen.
//
// Here both overloads are viable for an lvalue `int*` argument and their
// implicit conversion sequences are indistinguishable (identity for f(T*);
// lvalue-to-const-reference binding for f(const U&) -- both rank as an exact
// match for an lvalue argument).  Overload resolution must therefore fall back
// to partial ordering, under which f(T*) is more specialized than f(const U&):
// deducing U from a synthesized X* succeeds (U = X*), but deducing T* from a
// synthesized (const) Y fails (Y is not a pointer).  So f(T*) is selected and
// `r == 1`.
//
// This is the header-free analogue of libstdc++ std::to_address, whose call to
//   __to_address(_Tp*)            // raw, more specialized
//   __to_address(const _Ptr&)     // fancy-pointer fallback
// with the lvalue pointer parameter ties and, without partial ordering, reports
// "does not uniquely resolve" -- breaking std::span's _M_ptr (see cpp20_span).
//
// The assertion is non-vacuous: if the wrong overload were chosen, r == 2.
template <typename T>
int f(T *)
{
  return 1;
}
template <typename U>
int f(const U &)
{
  return 2;
}

int main()
{
  int x = 0;
  int *p = &x; // lvalue pointer argument
  int r = f(p);
  __CPROVER_assert(r == 1, "f(T*) is more specialized than f(const U&)");
  return 0;
}
