// Aggregate initialization with brace elision for structs that have
// type-alias components (typedefs) before data members.
// The designator index must account for non-data components.
#include <array>

template <typename T, int N>
struct myarray
{
  typedef T value_type;
  typedef T *pointer;
  T _M_elems[N];
  T &operator[](int i)
  {
    return _M_elems[i];
  }
};

int main()
{
  // Custom array-like struct with typedefs before data member
  myarray<int, 3> a = {1, 2, 3};
  __CPROVER_assert(a[0] == 1, "custom first");
  __CPROVER_assert(a[1] == 2, "custom second");
  __CPROVER_assert(a[2] == 3, "custom third");

  // std::array aggregate initialization
  std::array<int, 3> b = {10, 20, 30};
  __CPROVER_assert(b[0] == 10, "std first");
  __CPROVER_assert(b[1] == 20, "std second");
  __CPROVER_assert(b[2] == 30, "std third");
}
