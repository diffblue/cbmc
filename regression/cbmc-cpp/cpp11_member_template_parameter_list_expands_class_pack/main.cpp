extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.inst]/3, [temp.variadic]/5: in a member function template of a
// class template specialization, the class's parameter pack V is already
// bound -- `V...' is a list of ordinary parameters, which need not be the
// trailing ones (the MSVC STL's _Meta_at_impl<void *, ...>::_Eval)
template <class... V>
struct S
{
  template <class T>
  static int index(V..., T *)
  {
    return sizeof...(V);
  }
};
int main()
{
  long *p = nullptr;
  __CPROVER_assert(
    S<>::index(p) == 0 && S<void *, int>::index(nullptr, 1, p) == 2,
    "T deduced after the class pack");
  __CPROVER_assert(S<void *>::index(nullptr, p) == 0, "WRONG (must FAIL)");
  return 0;
}
