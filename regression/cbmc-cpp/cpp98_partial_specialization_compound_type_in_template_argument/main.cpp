// N5008 [temp.spec.partial.match]/2, [temp.deduct.type]/8-9: a partial
// specialization's template argument may be a compound type built from a
// parameter inside a template-id: `K<box<R *>>' matches K<box<int *>>
// with R = int, but not K<box<int>>.  The deduction compared the argument
// node, not its type, so it never matched and the primary template was
// used.  libstdc++'s __gen_vtable_impl<_Multi_array<_Result_type
// (*)(_Visitor, _Variants...)>, ...> (std::visit) has this shape.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct box
{
};

template <class A>
struct K
{
  static const int n = 1;
};
template <class R>
struct K<box<R *>>
{
  static const int n = 2;
};
template <class R>
struct K<box<const R>>
{
  static const int n = 3;
};
template <class A>
struct L
{
  static const int n = 1;
};
template <class R>
struct L<box<R (*)(char)>>
{
  static const int n = 4;
};

template <class T>
int f(box<T *>)
{
  return 5;
}
int f(...)
{
  return 6;
}

int main()
{
  __CPROVER_assert(K<box<int *>>::n == 2, "pointer");
  __CPROVER_assert(K<box<const int>>::n == 3, "const");
  __CPROVER_assert(L<box<int (*)(char)>>::n == 4, "function pointer");
  __CPROVER_assert(K<box<int>>::n == 1, "primary");
  __CPROVER_assert(f(box<int *>{}) == 5, "function template");
  __CPROVER_assert(f(box<int>{}) == 6, "no deduction");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
