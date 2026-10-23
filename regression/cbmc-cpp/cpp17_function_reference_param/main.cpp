#include <cassert>
#include <functional>

// std::function<R(Args...)> is a partial specialization over a function
// type.  When an argument is a reference (e.g. const int &), the
// specialization must still be selected so that members such as the
// explicit operator bool and operator() are available.  Regression for
// "invalid implicit conversion from 'struct function' to '__CPROVER_bool'"
// on std::function with a reference parameter.

int main()
{
  std::function<int(const int &)> g;
  assert(!g);
  g = [](const int &x) { return x + 1; };
  assert(static_cast<bool>(g));
  assert(g(41) == 42);
  return 0;
}
