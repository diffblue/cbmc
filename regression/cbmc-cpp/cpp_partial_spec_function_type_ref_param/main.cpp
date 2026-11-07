// A class template partial specialization whose pattern is a function
// type must be selected when a parameter of the argument function type
// is a reference or pointer ([temp.deduct.type]: a function parameter's
// reference/pointer is part of the type and must be deduced as such).
// Previously the reference/pointer was dropped during deduction, so the
// (incomplete) primary template was used instead of the specialization.

template <class>
struct fn_traits;

template <class R, class A>
struct fn_traits<R(A)>
{
  static const int arity = 1;
};

int main()
{
  static_assert(fn_traits<int(const int &)>::arity == 1, "reference param");
  static_assert(fn_traits<int(int *)>::arity == 1, "pointer param");
  static_assert(fn_traits<int(int)>::arity == 1, "value param");
  return 0;
}
