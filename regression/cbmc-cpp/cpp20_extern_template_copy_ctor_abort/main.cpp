// cvise-reduced from a preprocessed libc++ <vector> driver: an
// `extern template` declaration of a copy constructor whose class has
// another constructor taking an alias of a NESTED INCOMPLETE class
// template chain (__size_type<...<__pointer<int>>>, where __pointer's
// default argument uses the clang builtin __remove_reference_t)
// ABORTS the front end when the copy constructor is invoked:
// Invariant "expr.function().id() == ID_member" in
// typecheck_method_application (cpp_typecheck_expr.cpp).  This crash
// masks all preprocessed-libc++ reductions (vector semantic family,
// ranges silent drop, set_insert).  clang++/valgrind run clean
// (clang-only builtin; g++ n/a).

extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp>
using __libcpp_remove_reference_t = __remove_reference_t(_Tp);
template <class _Alloc, class = __libcpp_remove_reference_t<_Alloc>>
struct __pointer;
template <class> struct __size_type;
template <class> struct __alloc_traits_difference_type;
using size_type = __size_type<__alloc_traits_difference_type<__pointer<int>>>;
template <class> struct basic_string {
  typedef int value_type;
  int v;
  basic_string() : v(1) {}
  basic_string(size_type);
  basic_string(const basic_string &o) : v(o.v) {}
  void __init(const value_type *, size_type, size_type);
};
extern template void basic_string<char>::__init(value_type const *, size_type,
                                                size_type);
extern template basic_string<char>::basic_string(basic_string const &);
int copy_it(const basic_string<char> &b) {
  basic_string<char> t = b;
  return t.v;
}
int main() {
  basic_string<char> s;
  __CPROVER_assert(copy_it(s) == 1, "copy ctor typechecks");
  return 0;
}

// pair the extern template declaration with the explicit
// instantiation so the program links stand-alone
template basic_string<char>::basic_string(basic_string const &);
