template <typename T, typename U>
concept SameAs = __is_same(T, U);

// Concept with template arguments as parameter constraint
template <typename T, SameAs<T> U>
T add(T a, U b)
{
  return a + b;
}

// Qualified concept name
namespace detail
{
template <typename T>
concept Integral = __is_same(T, int);
}

template <detail::Integral T>
T identity(T x)
{
  return x;
}

// Constructor with trailing requires clause
template <typename T>
struct Wrapper
{
  T val;
  Wrapper(T v) requires SameAs<T, int> : val(v)
  {
  }
};

int main()
{
  int r1 = add(1, 2);
  __CPROVER_assert(r1 == 3, "add works");

  int r2 = identity(42);
  __CPROVER_assert(r2 == 42, "identity works");

  Wrapper<int> w(10);
  __CPROVER_assert(w.val == 10, "wrapper works");
}
