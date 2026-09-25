// libc++-20 std::endl template argument deduction
#include <iostream>
int main()
{
  std::endl(std::cerr);   // direct call: [temp.deduct.call]
  std::cerr << std::endl; // function pointer: [temp.deduct.funcaddr]
  return 0;
}
