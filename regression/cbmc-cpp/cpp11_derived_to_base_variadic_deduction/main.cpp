// N5008 [temp.deduct.call]/4: when a function parameter is a reference to a
// class template specialization `Base<...>&` and the argument is of a class type
// derived from a specialization of `Base`, template argument deduction is
// performed against that base-class specialization ("derived-to-base"
// deduction) -- including when the argument's class is NOT itself a template
// specialization (a plain `struct D : Base<...>`), and including when the base's
// trailing template parameter pack deduces to a non-empty pack.
//
// Regression: CBMC aborted deduction whenever the argument type was not itself
// instantiated from a template (an `is_nil` guard on its recorded template),
// which rejected a plain derived class before the derived-to-base dispatch could
// run.  Fixed by walking the argument class's bases for a specialization of the
// deduced template and retrying deduction against it.
//
// This is the shape behind std::get<I> on std::tuple, whose `__get_helper<I>`
// deduces `_Tuple_impl<I, Head, Tail...>` from the (derived) tuple.
//
// Non-vacuity: `f<0>` and `f<1>` deduce different elements (int vs char) of the
// derived-to-base-matched specialization, and the explicit index selects a
// deeper base of the recursively-inheriting `impl`.

extern "C" void __CPROVER_assert(int, const char *);

template <unsigned I, class... T>
struct impl;
template <unsigned I>
struct impl<I>
{
};
template <unsigned I, class H, class... T>
struct impl<I, H, T...> : impl<I + 1, T...>
{
};

// A plain (non-template) class deriving from a recursively-inheriting base.
struct D : impl<0, int, char>
{
};

template <unsigned I, class H, class... T>
unsigned f(impl<I, H, T...> &)
{
  return sizeof(H);
}

int main()
{
  D d;
  // f<0> deduces impl<0, int, char> (Head = int, Tail = {char}: a non-empty
  // trailing pack deduced from a base subobject of a non-template derived
  // class).
  __CPROVER_assert(
    f<0>(d) == sizeof(int), "derived-to-base deduction: head element (int)");
  // f<1> deduces the deeper base impl<1, char> (Head = char).
  __CPROVER_assert(
    f<1>(d) == sizeof(char), "derived-to-base deduction: deeper base (char)");
  return 0;
}
