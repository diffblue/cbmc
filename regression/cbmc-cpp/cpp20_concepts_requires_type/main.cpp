// requires-expression with type requirements:
// requires { typename T::type; } checks if T has a member type 'type'

// Primary template
template <class T>
struct get_inner
{
  typedef T type;
};

// Constrained specialization: only matches when T has value_type
template <class T>
requires requires
{
  typename T::value_type;
}
struct get_inner<T>
{
  typedef typename T::value_type type;
};

struct Container
{
  typedef double value_type;
};

int main()
{
  // With full concept evaluation:
  // get_inner<int>::type should be int (primary, int has no value_type)
  // get_inner<Container>::type should be double (specialization)
  //
  // Without concept evaluation, CBMC skips the requires clause and
  // always tries the specialization. For int, this fails because
  // int::value_type doesn't exist, causing a type-checking error
  // that's suppressed. The primary template is then used, giving int.
  // For Container, the specialization works, giving double.
  //
  // The test checks that both paths produce correct results.
  // Currently get_inner<int> falls back to primary (int) after the
  // specialization fails, so both assertions should pass.
  // But the error message "scope 'T' not found" indicates the
  // requires clause is not being properly evaluated.

  get_inner<Container>::type x = 1.5;
  __CPROVER_assert(x > 1.0, "Container inner type is double");

  get_inner<int>::type y = 42;
  __CPROVER_assert(y == 42, "int inner type is int");
}
