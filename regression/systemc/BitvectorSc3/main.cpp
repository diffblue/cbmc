#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

//#define IO

#ifdef IO
#include <iostream>
#include <bitset>
#endif

int main(int argc, char** argv)
{
  //TODO: declaration alone doesn't type-check
  sc_uint<8> x(221); //11011101
  sc_uint<4> y(5);  //0101
  sc_uint<4> z(12);  //1100

#ifdef IO
  std::cout << "x = " << std::bitset<MAX_SIZE>(x.to_uint()) << std::endl;
  std::cout << "x.length() = " << x.length() << std::endl;
  std::cout << "y = " << std::bitset<MAX_SIZE>(y.to_uint()) << std::endl;
  std::cout << "z = " << std::bitset<MAX_SIZE>(z.to_uint()) << std::endl;
  std::cout << "x.range(4,1) = " << std::bitset<MAX_SIZE>(x.range(4,1).to_uint()) << std::endl;
  std::cout << "x.range(4,1).length() = " << x.range(4,1).length() << std::endl;
#endif

  x.range(4,1) = y; //1110 replaced by 0101
  y = x.range(7,4); //1100

#ifdef IO
  std::cout << "x = " << std::bitset<MAX_SIZE>(x.to_uint()) << std::endl;
  std::cout << "x.range(4,1) = " << std::bitset<MAX_SIZE>(x.range(4,1).to_uint()) << std::endl;
  std::cout << "x.range(4,1).length() = " << x.range(4,1).length() << std::endl;
  std::cout << "x.range(7,4) = " << std::bitset<MAX_SIZE>(x.range(7,4).to_uint()) << std::endl;
  std::cout << "x.range(7,4).length() = " << x.range(7,4).length() << std::endl;
  std::cout << "y = " << std::bitset<MAX_SIZE>(y.to_uint()) << std::endl;
#endif

  assert(y == z);

  return 0;
}
