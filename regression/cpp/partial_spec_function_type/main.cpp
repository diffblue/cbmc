// Partial specialization matching for function types.
// Wrapper<R(A)> should match Wrapper<bool(char)>.

#include <assert.h>

template <typename T>
struct Wrapper;

template <typename R, typename A>
struct Wrapper<R(A)>
{
  typedef R return_type;
  int x;
};

int main()
{
  Wrapper<bool(char)> w;
  w.x = 42;
  assert(w.x == 42);
}
