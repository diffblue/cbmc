// [temp.deduct.funcaddr] fails for endl used as function pointer
// argument to operator<< when basic_ostream lacks template metadata.
#include <iostream>
int main()
{
  std::cerr << "Test" << std::endl;
  return 0;
}
