// Template argument deduction fails for forward-declared
// template instantiations that lack ID_C_template metadata.
// endl(cerr) requires deducing _CharT and _Traits from cerr's type.
#include <iostream>
int main()
{
  std::endl(std::cerr);
  return 0;
}
