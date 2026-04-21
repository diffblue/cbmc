// Same as cpp20_concepts_ordering but for GCC 14.2+ where
// __is_pointer/__remove_pointer builtins interact differently
// with the system headers.
template <class T>
struct category
{
  static const int value = 0;
};

template <class T>
requires(__is_pointer(T)) struct category<T>
{
  static const int value = 1;
};

template <class T>
requires(
  __is_pointer(T) && __is_integral(__remove_pointer(T))) struct category<T>
{
  static const int value = 2;
};

int main()
{
  __CPROVER_assert(category<double>::value == 0, "non-pointer");
  __CPROVER_assert(category<double *>::value == 1, "pointer to non-integral");
  __CPROVER_assert(category<int *>::value == 2, "pointer to integral");
}
