// GCC 13+ and clang treat __remove_cv, __remove_reference and __remove_cvref
// as "revertible" builtins: keywords only when directly followed by '('.
// A translation unit preprocessed by such a gcc (a .ii) uses them regardless
// of the host gcc's version, which used to gate the scanner.
extern "C" void __CPROVER_assert(bool, const char *);
template <class A, class B>
struct is_same
{
  static const bool value = false;
};
template <class A>
struct is_same<A, A>
{
  static const bool value = true;
};

int main()
{
  typedef int &&rref;
  typedef const int &cref;
  static_assert(is_same<__remove_cv(const int), int>::value, "builtin");
  static_assert(
    is_same<__remove_reference(rref), int>::value, "builtin reference");
  static_assert(is_same<__remove_cvref(cref), int>::value, "cvref");
  // N5008 [meta.trans.other]/3: the reference is removed first, then the
  // cv-qualifiers of the referenced type
  static_assert(
    is_same<__remove_cvref(const volatile int &), int>::value, "cvref order");
  __CPROVER_assert(sizeof(__remove_cv(const char)) == 1, "builtin type");
  return 0;
}
