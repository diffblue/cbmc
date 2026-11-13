// std::vector::at throws std::out_of_range ([vector.overview],
// [sequence.reqmts]/122) through libstdc++'s __throw_out_of_range_fmt,
// defined in the compiled library.  CBMC models it by throwing an
// out_of_range, but <vector> alone does not declare that class: the call
// was left to return, as one of a function without a body.  No handler
// can name an undeclared class ([except.handle]/3); std::exception, its
// base ([std.exceptions]/1), is thrown instead.
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector<int> v(1);
  bool caught = false;
  try
  {
    v.at(5);
    __CPROVER_assert(false, "not reached: at() throws");
  }
  catch(std::exception &)
  {
    caught = true;
  }
  __CPROVER_assert(caught, "caught as std::exception");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
