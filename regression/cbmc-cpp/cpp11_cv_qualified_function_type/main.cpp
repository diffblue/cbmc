// N5008 [dcl.fct]/7: "The effect of a cv-qualifier-seq in a function declarator
// is not the same as adding cv-qualification on top of the function type.  In
// the latter case, the cv-qualifiers are ignored.  [Note: A function type that
// has a cv-qualifier-seq is not a cv-qualified type; there are no cv-qualified
// function types. -- end note]"
//
// So when a cv-qualified template parameter `const T` is substituted with a
// function type, the const must be dropped (the result is the plain function
// type, which is NOT const-qualified).  This is exactly how libstdc++ (gcc 13)
// implements std::is_function:
//   template<class T> struct is_function : bool_constant<!is_const<const T>::value> {};
// a function type F is "not const" (const F is ignored) so is_function<F> is
// true; an object type is const when const-qualified so is_function is false.
// std::decay relies on is_function for function-to-pointer decay, and
// std::function relies on decay of its (function) target -- so this underlies
// constructing a std::function from a plain function.
//
// Bug: const applied to a function-typed template parameter via substitution
// was written onto the function type, so `is_const<const T>` was wrongly true
// and `is_function<F>` wrongly false.
//
// Header-free and non-vacuous (assertion 4 must FAIL).

extern "C" void __CPROVER_assert(int, const char *);

template <class>
struct ic
{
  static const bool value = false;
};
template <class T>
struct ic<const T>
{
  static const bool value = true;
};

// is_function the libstdc++ way: a cv-qualifier on a function type is ignored.
template <class T>
struct isfunc
{
  static const bool value = !ic<const T>::value;
};

int main()
{
  __CPROVER_assert(isfunc<int(int)>::value, "function type is a function");
  __CPROVER_assert(
    isfunc<int(int, int)>::value, "multi-arg function type is a function");
  __CPROVER_assert(!isfunc<int>::value, "object type is not a function");
  __CPROVER_assert(!isfunc<int(int)>::value, "WRONG must FAIL");
  return 0;
}
