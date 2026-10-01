extern "C" void __CPROVER_assert(bool, const char *);
// GCC's (and Clang's) __decay(T) builtin, libstdc++ 16's std::decay: N5008
// [meta.trans.other] decay<T> -- with U = remove_reference_t<T>, an array
// of U becomes a pointer to its element type, a function type a pointer to
// it, any other type remove_cv_t<U>
template <typename T, typename U>
constexpr bool same = __is_same(T, U);
int main()
{
  __CPROVER_assert(same<__decay(const volatile int &), int>, "cv-qualified");
  __CPROVER_assert(same<__decay(int *const), int *>, "top-level const");
  __CPROVER_assert(same<__decay(int[5]), int *>, "array");
  __CPROVER_assert(same<__decay(int(&)[5]), int *>, "reference to array");
  __CPROVER_assert(same<__decay(const int[]), const int *>, "unknown bound");
  __CPROVER_assert(same<__decay(int (&)(long)), int (*)(long)>, "function");
  __CPROVER_assert(!same<__decay(int[5]), int *>, "WRONG (must FAIL)");
}
