// Constructing an object with a functional/explicit cast from a
// reference-typed operand -- e.g. `T(static_cast<A&&>(a))`, the form
// produced by std::forward inside a function template -- must perform the
// usual reference-binding / lvalue-to-rvalue conversion on the operand
// ([expr.type.conv], [conv.lval]).  Previously CBMC passed the
// reference-typed operand straight to its cast helpers, tripping
// const_typecast's "operand is not a reference" precondition.

template <class T>
struct Wrap
{
  T value;
  template <class... A>
  void assign(A &&...a)
  {
    value = T(static_cast<A &&>(a)...);
  }
};

template <class T>
T make(T &&x)
{
  return T(static_cast<T &&>(x));
}

int main()
{
  Wrap<int> w;
  w.assign(42);
  __CPROVER_assert(w.value == 42, "functional cast from forwarded reference");

  int i = make(7);
  __CPROVER_assert(i == 7, "single-arg functional cast from forwarded ref");

  return 0;
}
