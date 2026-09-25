// An `auto`-returning static member of a class template, called from a
// function template being typechecked at instantiation time.  Per N5008
// [dcl.spec.auto.general]/13 the deduced return type comes from the
// definition and must be available where the type is needed; CBMC used
// to queue the member body like any other method, so the call site in
// `wrap` typechecked against the undeduced placeholder and the whole
// `wrap<int>` instance was silently dropped to a no-body stub.
// Reduced from libc++'s __unwrap_range_impl::__unwrap (the second
// layer of the vector push_back family).
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct impl
{
  static auto get(T x)
  {
    return x;
  }
};

template <class T>
int wrap(T x)
{
  return impl<T>::get(x);
}

int main()
{
  __CPROVER_assert(wrap(7) == 7, "val");
}
