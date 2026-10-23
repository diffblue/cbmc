// Constraint-based partial specialization ordering:
// when multiple constrained specializations match, the most
// constrained one should be selected.

template <class T>
struct category
{
  static const int value = 0;
};

// Specialization for pointer types
template <class T>
requires(__is_pointer(T)) struct category<T>
{
  static const int value = 1;
};

// More constrained: pointer to integral
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
