#include <functional>

struct dstringt
{
  int x;
};

// Regression for a function-type template argument whose parameter is
// named.  Per [dcl.fct]/3 a parameter name is not part of the function
// type, so std::function<void(const dstringt &id)> denotes the same
// specialization as std::function<void(const dstringt &)>.  Having the
// named type both as a data member and as a by-value constructor
// parameter previously produced a distinct, never-elaborated
// instantiation, so the contextual conversion to bool in `ready()` was
// wrongly rejected with "invalid implicit conversion from 'struct
// function' to '__CPROVER_bool'".  This is a front-end (type-checking)
// regression test: the translation unit must compile without a
// CONVERSION ERROR.
struct holder
{
  std::function<void(const dstringt &id)> on_get;

  holder()
  {
  }

  explicit holder(std::function<void(const dstringt &id)> g)
    : on_get(std::move(g))
  {
  }

  bool ready()
  {
    if(on_get)
      return true;
    return false;
  }
};

int main()
{
  holder h;
  return h.ready() ? 1 : 0;
}
