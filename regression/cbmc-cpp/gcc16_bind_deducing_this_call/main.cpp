// libstdc++ 16's std::_Bind::operator() is declared with an explicit object
// parameter (C++23 [dcl.fct]/6, `this _Self &&__self') and constrained by
// the default template argument `__enable_if_t<!is_volatile<_Self_nonref>
// ::value, int> = 0'.  Calling the bind expression finds no viable
// operator() ("found no match for symbol 'operator()'"): deduction of the
// explicit object parameter's type from the object expression does not
// reach the enable_if default argument.
#include <functional>
extern "C" void __CPROVER_assert(bool, const char *);
int add(int a, int b)
{
  return a + b;
}
int main()
{
  auto f = std::bind(add, 1, std::placeholders::_1);
  __CPROVER_assert(f(2) == 3, "bind expression call");
  return 0;
}
